// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package squid
package ir

import utils._
import utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.sru
import squid.lang.Base

import scala.collection.mutable


/** Useful utility methods used by AST */
trait ASTHelpers extends Base { self: AST =>
  
  
  // TODO implement and use `traverse` method here
  def hasImmediateHoles(r: Rep): Boolean = r |> traversePartial { 
    case RepDef(Abs(_,_)) => false
    case RepDef(Hole(_)|SplicedHole(_)) => return true
  } thenReturn false
  
  def traversePartial(f: PartialFunction[Rep, Boolean]) = traverse(f orElse { case _ => true }) _
  
  def traverse(f: Rep => Boolean)(r: Rep): Unit = {
    val rec = if (f(r)) traverse(f) _ else ignore
    dfn(r) match {
      case a @ Abs(p, b) => rec(b)
      case Ascribe(r,t) => rec(r)
      case Module(pref, name, typ) => rec(pref)
      case MethodApp(self, mtd, targs, argss, tp) =>
        rec(self)
        argss.foreach(_.reps foreach rec)
      case Hole(_) | SplicedHole(_) | NewObject(_) | StaticModule(_) | _:ConstantLike | _: BoundVal =>
    }
  }
  
  object ByName {
    val VAL_NAME = "$BYNAME$"
    def apply(arg: Rep): Rep =
      lambda(bindVal(VAL_NAME, uninterpretedType[Unit], Nil) :: Nil, arg) // FIXME proper impl  TODO use annot
    def unapply(arg: Rep): Option[Rep] = unapply(arg |> dfn)
    def unapply(arg: Def) = arg match {
      case Abs(BoundVal(VAL_NAME), b) => b |> some
      case _ =>
        //println("Not by name: "+arg)
        None
    }
  }
  
  object Apply {
    val Symbol = ruh.FunctionType.symbol().toType.member(sru.TermName("apply")).asMethod // TODO use loadMtdSymbol
    def apply(f: Rep, a: Rep, typ: TypeRep) = MethodApp(f, Symbol, Nil, Args(a)::Nil, typ)
    def unapply(d: Def): Option[Rep -> Rep] = d match {
      case MethodApp(f, Symbol, Nil, Args(a)::Nil, _) => Some(f -> a)
      case _ => None
    }
    def unapply(r: Rep): Option[Rep -> Rep] = unapply(dfn(r))
  }
  object LetIn {
    def apply(p:Val,v:Rep,b:Rep): Def = Apply(rep(Abs(p,b)(b.typ)),v,b.typ)
    def unapply(d: Def): Option[(Val, Rep, Rep)] = d match {
      case Apply(RepDef(Abs(p,b)),v) => Some(p,v,b)
      case Apply(RepDef(Ascribe(RepDef(Abs(p,b)),_)),v) =>
        // Should probably propagate the info in the ascribed type by ascribing the body and the uses of `v` in the body...
        Some(p,v,b)
      case _ => None
    }
    def unapply(r: Rep): Option[(Val, Rep, Rep)] = unapply(dfn(r))
  }
  
  // TODO implement helpers to ease method loading : method[Tp](name) or method[Tp](_.mtd(???...)), or using QQ: ir"($$_:Int)+($$_:Int)".method?
  object Imperative {
    val Symbol = loadMtdSymbol(loadTypSymbol("squid.lib.package$"), "Imperative", None)
    def apply(effects: Seq[Rep], res: Rep) = {
      require(effects nonEmpty)
      MethodApp(staticModule("squid.lib.package"), Symbol, res.typ::Nil, ArgsVarargs(Args(),Args(effects: _*))::Args(res)::Nil, res.typ) // TODO factor below
    }
    def apply(effects: Rep*)(res: Rep) = if (effects isEmpty) res else
      rep(MethodApp(staticModule("squid.lib.package"), Symbol, res.typ::Nil, ArgsVarargs(Args(),Args(effects: _*))::Args(res)::Nil, res.typ))
    def unapply(r: Rep): Option[(Seq[Rep], Rep)] = unapply(dfn(r))
    def unapply(d: Def) = d match {
      case MethodApp(self, Symbol, _::Nil, ArgsVarargs(Args(),Args(effs @ _*))::Args(res)::Nil, _) => Some(effs, res)
      case _ => None
    }
  }
  
  object Var {
    val ModuleSymbol = loadTypSymbol("squid.lib.package.MutVar$")
    val ClassSymbol = loadTypSymbol("squid.lib.package.MutVar")
    object Apply {
      val Symbol = loadMtdSymbol(ModuleSymbol, "apply", None)
    }
    object Bang { val Symbol = loadMtdSymbol(ClassSymbol, "$bang", None) }
    object ColonEqual { val Symbol = loadMtdSymbol(ClassSymbol, "$colon$eq", None) }
  }
  
  
  // TODO move these into a Builtin object
  lazy val UnitType = staticTypeApp(loadTypSymbol("scala.Unit"),Nil)
  lazy val NothingType = staticTypeApp(loadTypSymbol("scala.Nothing"),Nil)
  
  
  // Q: use a reinterpreter? (cf: would facilitate the work for Args)
  def prettyPrint(d: Def) = (new DefPrettyPrinter)(d)
  class DefPrettyPrinter {
    
    val showReturnTypes = false
    val showMtdReturnType = showReturnTypes
    val showHoleInfo = false
    
    var ident = 0
    def apply(r: Rep): String = apply(dfn(r))
    def apply(d: Def): String = d match {
      case Constant(str: String) => '"' + str + '"'
      case Constant(v) => s"$v"
      case NewObject(typ) => s"new ${typ |> apply}"
      case Typed(BoundVal(name), typ) => s"[$name:${typ |> apply}]"
      case Abs(p, b) => s"{$p => ${apply(b)}}"
      case LetIn(p, v, b) => s"let $p = ${apply(v) alsoDo (ident += 2)} in${s"->${b.typ}" optionIf showReturnTypes Else ""}\n${try " " * ident + apply(b) finally ident -= 2}"
      //case Imperative(effs, res) => s"{ ${effs map apply mkString "; "}; $res }"
      case imp@Imperative(effs, res) => s"{\n${ident += 2; try ((effs :+ res) map apply map (" " * ident + _ + "\n") mkString) finally ident -= 2}${" " * ident}}${s"->${imp.typ}" optionIf showReturnTypes Else ""}"
      case MethodApp(s, m, ts, ass, typ) => 
        val targsStr = if (ts isEmpty) "" else s"[${ts mkString ","}]"
        s"${apply(s)}.${m.name.decodedName}$targsStr${ass map (_ show apply) mkString ""}" + (if (showMtdReturnType) s"->${typ |> apply}" else "")
      case Module(pre, nam, tp) => s"${apply(pre)}.$nam"
      case StaticModule(fnam) => fnam
      case Ascribe(r,t) => s"${apply(r)}: ${t |> apply}"
      case Typed(h @ Hole(name), typ) => s"$$$name<:${typ |> apply}" + (if (showHoleInfo) 
        (h.originalSymbol map (os => s"(o=$os)") getOrElse "") + (h.matchedSymbol map (m => s"(m=$m)") getOrElse "") else "")
      case Typed(SplicedHole(name), typ) => s"$$$name<:${typ |> apply}*"
      case CrossStageValue(value,typ) if showReturnTypes => s"<<$value:${typ |> apply}>>"
      case CrossStageValue(value,typ)                    => s"<<$value>>"
    }
    def apply(typ: TypeRep) =
      typ.toString.replace("squid.ir.ScalaTyping.TypeHole[java.lang.String", "$[")
  }
  
  
  /** Provides some useful debugging when a merge fails. */
  override protected def merge(a: Extract, b: Extract): Option[Extract] = {
    //if (extractedKeys(a).nonEmpty && extractedKeys(b).nonEmpty) debug(s"Merging: ${a|>extractedKeys} with ${b|>extractedKeys}")
    val res = super.merge(a, b)
    if (res.isEmpty && isDebugEnabled) {
      debug(s"Could not merge Extract's:")
      debug("\t"+a)
      debug("\t"+b)
      val collTerms =
        for (k <- a._1.keySet intersect b._1.keySet; v0 = a._1(k); v1 = b._1(k); if !mergeableReps(v0,v1)) yield v0 -> v1
      if (collTerms nonEmpty) {
        debug(s"Colliding simple terms:")
        for (v0 -> v1 <- collTerms) debug(s"\t$v0  <>  $v1")
      }
      val collTyps =
        for (k <- a._2.keySet intersect b._2.keySet; v0 = a._2(k); v1 = b._2(k); if mergeTypes(v0,v1) isEmpty) yield v0 -> v1
      if (collTyps nonEmpty) {
        debug(s"Colliding types:")
        for (v0 -> v1 <- collTyps) debug(s"\t$v0  <>  $v1")
      }
      if (a._3 nonEmpty) debug(s"(Perhaps some spliced terms collide.)")
    }
    res
  }
  
  
  protected def unboundVals(d: Def): Set[Val] = d match {
    case bv: BoundVal => Set(bv)
    case Abs(p,b) => dfn(b).unboundVals - p
    case _ => d.children.foldLeft(Set.empty[Val]){ (s,df) => s ++ dfn(df).unboundVals }
  }
  def freeVariables(r: Rep): Set[BoundVal] = unboundVals(dfn(r))
  
  
  abstract override def loadTypSymbol(fullName: String) = {
    try super.loadTypSymbol(fullName)
    catch {
      case e @ ScalaReflectionException(msg) =>
        throw TypSymbolLoadingException(fullName, e)
    }
  }
  abstract override def loadMtdSymbol(typ: ScalaTypeSymbol, symName: String, index: Option[Int], static: Boolean = false): MtdSymbol = {
    try super.loadMtdSymbol(typ, symName, index, static)
    catch {
      case e @ ScalaReflectionException(msg) =>
        throw MtdSymbolLoadingException(typ, symName, index, e)
    }
  }
  
}

