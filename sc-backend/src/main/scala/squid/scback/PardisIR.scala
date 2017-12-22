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
package scback

import ch.epfl.data.sc._
import ch.epfl.data.sc.pardis.ir.{Base => _, _}
import ch.epfl.data.sc.pardis.prettyprinter.ScalaCodeGenerator
import ch.epfl.data.sc.pardis.types.{PardisTypeImplicits, PardisType}
import pardis._
import pardis.{ir => pir}
import squid.utils._
import CollectionUtils.TraversableOnceHelper
import ch.epfl.data.sc.pardis.deep.scalalib.collection.CanBuildFromIRs.CanBuildFromType
import ch.epfl.data.sc.pardis.types

import scala.collection.mutable
import meta.{RuntimeUniverseHelpers => ruh}
import meta.RuntimeUniverseHelpers.sru
import squid.ir.IRException
import squid.ir.{Covariant, Variance}
import squid.lang.Base
import squid.lang.InspectableBase
import squid.scback.PardisBinding.ExtractedBinderType
import sun.reflect.generics.reflectiveObjects.NotImplementedException

import scala.language.existentials
import scala.reflect.runtime.universe.TypeTag


/** IR Base that uses SC as a backend. It constructs PardisType's via reflective invocation of methods found in `ir`
  * Note: For convenience, we use Scala MethodSymbol and TypeSymbol to identify methods and types, but we could do with
  *   a simpler representation. */
abstract class PardisIR(val sc: pardis.ir.Base) extends Base with squid.ir.RuntimeSymbols with InspectableBase { self =>
  import sc.Def
  
  type Rep = ANFNode
  type BoundVal = sc.Sym[_]
  type TypeRep = sc.TypeRep[Any]
  type Expr = sc.Rep[_]
  type Block = sc.Block[_]
  type ABlock = sc.Block[Any]
  type Sym = sc.Sym[_]
  type ASym = sc.Sym[Any]
  type Stm = sc.Stm[_]
  type AStm = sc.Stm[Any]
  type Var = sc.Var[Any]
  
  type R[+A] = sc.Rep[A]
  type TR[A] = sc.TypeRep[A]
  
  type TypSymbol = ScalaTypeSymbol
  
  
  case class New[A](_tp: TR[A]) extends Expression[A]()(_tp)
  
  sealed trait AnyHole[A] extends Expression[A] { val name: String }
  case class Hole[A](name: String, _tp: TR[A], originalSym: Option[BoundVal]) extends Expression[A]()(_tp) with AnyHole[A]
  case class SplicedHole[A](name: String, _tp: TR[A]) extends Expression[A]()(_tp) with AnyHole[A]
  
  case class HoleDef[A](h: AnyHole[A]) extends PardisNode[A]()(h.tp)
  
  
  case class TypeHole[A](name: String) extends PardisType[A] {
    def rebuild(newArguments: TR[_]*): TR[_] = this
    val typeArguments: List[TR[_]] = Nil
  }
  
  
  // TODO test support for varargs
  def varargsToPardisVarargs = ???
  
  
  
  // * --- * --- * --- *  Implementations of `Base` methods  * --- * --- * --- *
  
  final val NAME_SUFFIX = "_$"
  final val XTED_BINDER_SUFFIX = s"${NAME_SUFFIX}$$"
  // ^ Binders the user wants to extract are marked with two $$ (for example, in: `case ir"val $x = ..." => ...`)
  
  def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal = sc.freshNamed(
    if (annots.unzip._1 contains ExtractedBinderType)
      name+XTED_BINDER_SUFFIX
    else name+NAME_SUFFIX
  )(typ)
  
  def readVal(v: BoundVal): Rep = curSubs.getOrElse(v, v)
  
  def const(value: Any): Rep = {
    import types.PardisTypeImplicits._
    value match {
      case value: Unit => sc.unit(value)
      case value: Boolean => sc.unit(value)
      case value: Int => sc.unit(value)
      case value: Double => sc.unit(value)
      case value: String => sc.unit(value)
      case null => sc.unit(null)
      case _ =>
        println("Unsupported constant value: "+value)
        ??? // TODO
    }
  }
  def lambda(params: List[BoundVal], body: => Rep): Rep = {
    val b = typedBlock(toExpr(body))
    params match {
      case Nil =>
        val d = sc.Lambda0[Any](() => b |> toExpr, b)(b.tp)
        sc.toAtom(d)(types.PardisTypeImplicits.typeLambda0(b.tp))
      case p :: Nil =>
        val d = sc.Lambda[Any,Any]((x: Rep) => bottomUpPartial(b) { case `p` => x } |> toExpr, p, b)(p.tp, b.tp)
        sc.toAtom(d)(types.PardisTypeImplicits.typeLambda1(p.tp, b.tp))
      case p0 :: p1 :: Nil =>
        val d = sc.Lambda2[Any,Any,Any]((x0: Rep, x1: Rep) => bottomUpPartial(b) { case `p0` => x0 case `p1` => x1 } |> toExpr, p0, p1, b)(p0.tp, p1.tp, b.tp)
        sc.toAtom(d)(types.PardisTypeImplicits.typeLambda2(p0.tp, p1.tp, b.tp))
      case p0 :: p1 :: p2 :: Nil =>
        val d = sc.Lambda3[Any,Any,Any,Any]((x0: Rep, x1: Rep, x2: Rep) => bottomUpPartial(b) { case `p0` => x0 case `p1` => x1 case `p2` => x2 } |> toExpr, p0, p1, p2, b)(p0.tp, p1.tp, p2.tp, b.tp)
        sc.toAtom(d)(types.PardisTypeImplicits.typeLambda3(p0.tp, p1.tp, p2.tp, b.tp))
      case _ => throw new IRException("Unsupported function arity: "+params.size)
    }
  }
  override def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = {
    // we now put the result of let-bindings in blocks so their statements don't register before the stmts of Imperative
    // arguments that come before; this could be better solved with Imperative taking a by-name result (although it would
    // have the same effect); and better yet, having a Base method for imperative stuff (with scp.lib.Imperative only
    // used as a backup).
    blockWithType(bodyType)(
      value match {
        // In case the value bound here is a block that defines and returns a symbol, we want to inline it without
        // losing the original outer `bound` name!
        case sc.Block(sts,ret:ExpressionSymbol[Any @unchecked]) if sts.exists(_.sym == ret) =>
          var itsAVar = Option.empty[Var]
          sts foreach {
            case sc.Stm(`ret`,PardisReadVar(v)) => itsAVar = Some(v)
            case sc.Stm(`ret`,rhs) => reflect(sc.Stm(bound,rhs)(bound.tp))
            case s => reflect(s)
          }
          itsAVar match {
            // If the defined-and-returned symbol is the symbol of a variable, make sure to substitute symbol references
            // with the variable, which will produce a ReadVar node every time it is used. 
            case Some(v) =>
              withSubs(bound -> v)(body)
            case None => body
          }
        case b: Block =>
          val e = b |> inlineBlock
          withSubs(bound -> e)(body)
        case d: Def[_] =>  // Def <=> PardisNode
          reflect(sc.Stm[Any](bound, d)(bound.tp))
          body
        case h:AnyHole[_] => // todo generalize
          val d = HoleDef(h)
          reflect(sc.Stm[Any](bound, d)(bound.tp))
          body
        case e: Expr => withSubs(bound -> e)(body)
      }
    )
  }
  def newObject(tp: TypeRep): Rep = New(tp)
  def staticModule(fullName: String): Rep = null
  def module(prefix: Rep, name: String, typ: TypeRep): Rep = ???
  def byName(arg: => Rep): Rep = typedBlock(arg)
  
  object Const extends ConstAPI {
    def unapply[T: CodeType](ir: Code[T, _]): Option[T] = ir.rep match {
      case cst @ pir.Constant(v) if cst.typ <:< codeTypeOf[T].rep => Some(v.asInstanceOf[T])
      case _ => none
    }
  }
  
  def repEq(a: Rep, b: Rep): Boolean = a == b
  
  
  protected val curSubs = mutable.HashMap[Sym, Rep]()
  protected def withSubs[A](ss: (Sym -> Rep)*)(code: => A): A = {
    val keys = ss.unzip._1.toSet
    assert(curSubs.keySet intersect keys isEmpty)
    curSubs ++= ss
    try code
    finally curSubs --= keys
  }
  
  
  // Reimplementations
  
  override def showRep(r: Rep) = {
    import pardis.deep.scalalib.ArrayScalaCodeGen
    import ch.epfl.data.sc.pardis.prettyprinter.ASTCodeGenerator
    import ch.epfl.data.sc.pardis.utils.document.toDocumentContext
    val cg = new ScalaCodeGenerator with ASTCodeGenerator[sc.type] with ArrayScalaCodeGen {
      val IR: sc.type = sc
      override def expToDocument(exp: Expression[_]) = exp match {
        case Constant(b: Boolean) => doc"${b.toString}"
        case Hole(n,tp,Some(s)) => doc"($$$n: ${tp |> tpeToDocument} [from ${s |> symToDocument}])"
        case Hole(n,tp,None) => doc"($$$n: ${tp |> tpeToDocument})"
        case SplicedHole(n,tp) => doc"($$$n: ${tp |> tpeToDocument}*)"
        case _                    => super.expToDocument(exp)
      }
    }
    r match {
      case b: Block => cg.blockToDocument(b).toString
      case d: PardisNode[_] => cg.nodeToDocument(d).toString
        
      // A specialization of the one below to get some additional type info:
      case d: ExpressionSymbol[_] => cg.symToDocument(d).toString + ": " + cg.tpeToDocument(d.tp)
      case d: PardisFunArg => cg.funArgToDocument(d).toString
        
      case cn =>
        //println(cn)
        r.toString
    }
  }
  
  def boundValUniqueName(bv: BoundVal): String = s"$bv"
  
  def extractVal(r: Rep): Option[BoundVal] = r |>? { case bv: BoundVal => bv }
  
  // Helpers
  
  protected[squid] def blockWithType(tp: TypeRep)(body: => Rep): ABlock = {
    sc.reifyBlock[Any](toExpr(body))(tp)
  }
  protected[squid] def typedBlock(body: => Rep): ABlock = {
    val sc.Block(s,r) = sc.reifyBlock[Any](toExpr(body))(types.AnyType)
    sc.Block(s,r)(r.tp)
  }
  protected def toAtom(r: sc.Def[_]) = sc.toAtom[Any](r)(r.tp.asInstanceOf[TR[Any]])
  
  def inline[A,B,C](fun: Code[A => B,C], arg: Code[A,C]): Code[B,C] = {
    val fr = fun.rep match {
      case PardisLambda(f,_,_) => f
      case sc.Block(sc.Stm(s0,PardisLambda(f,_,_))::Nil,s1) if s0 == s1 => f
      case Def(PardisLambda(f,_,_)) => f
      case _ => throw new IRException(s"Unable to inline $fun")
    }
    ensureScoped(fr(arg.rep |> toExpr)) |> `internal Code`
  }
  protected def ensureScoped(x: => Rep) = if (sc._IRReifier.scopeDepth > 0) x else typedBlock(x)
  
  protected def reflect(s: Stm): Expr = {
    if (sc.IRReifier.scopeStatements.exists(_.sym == s.sym))  // eqt to `sc.IRReifier.findDefinition(sym).nonEmpty`
      sc.Stm(sc.freshNamed(s.sym.name)(s.sym.tp), s.rhs)(s.sym.tp) |> sc.reflectStm
    else s |> sc.reflectStm
  }
  
  // TODO better impl of this with a hashtable; this is uselessly linear!
  def inlineBlock(b: Block) = {
    require(sc.IRReifier.scopeDepth > 0, s"No outer scope to inline into for $b")
    b.stmts.asInstanceOf[Seq[AStm]] foreach reflect
    b.res
  }
  protected def inlineBlockIfEnclosed(b: Block) = {
    if (sc._IRReifier.scopeDepth > 0) {
      b.stmts.asInstanceOf[Seq[AStm]] foreach reflect
      b.res
    } else b
  }
  def toExpr(r: Rep): Expr = r match {
    case r: Expr => r
    case b: Block => inlineBlock(b)
    case d: Def[_] => toAtom(d)
    case v: PardisVar[_] => sc.__readVar[Any](v)(v.typ)
  }
  def toBlock(r: Rep): ABlock = r match {
    case b: sc.Block[Any @unchecked] => b
    case _ => sc.reifyBlock(r |> toExpr)(r.typ)
  }
  def toVar(r: Rep): sc.Var[Any] = r match {
    case v: PardisVar[Any @unchecked] => v
    case PardisReadVar(v) => v
    case sc.Def(PardisReadVar(v)) => v
    // A special case for allowing the following syntax in a context without enclosing block:
    //   val v = "Var(0)"; ir"$v.!"
    case b @ sc.Block((nv @ sc.Stm(v0, PardisNewVar(init))) :: sc.Stm(r0, PardisReadVar(v @ PardisVar(v1))) :: Nil, r1)
    if v0 == v1 && r0 == r1 =>
      if (sc.IRReifier.scopeStatements contains nv) () else sc.reflectStm(nv)
      v
    case _ => throw IRException(s"Cannot convert ${r} of class ${r.getClass} to a variable.")
  }
  
  
  
  // * --- * --- * --- *  Implementations of `QuasiBase` methods  * --- * --- * --- *
  
  protected def inlineUnlessEnclosedOr(dontInline: Bool)(r: Rep) = r |>=? {
    case b: Block if !dontInline => inlineBlockIfEnclosed(b)
  }
  override def substitute(r: => Rep, defs: Map[String, Rep]): Rep = substituteLazy(r, defs.mapValues(() => _))
  override def substituteLazy(mkR: => Rep, defs: Map[String, () => Rep]): Rep = {
    val r = if (defs isEmpty) mkR else typedBlock(mkR |> toExpr)
    //debug(s"SUBST $r with "+(defs mapValues (f=>util.Try(typedBlock(f())))))
    
    val nameMap = curSubs collect { case k -> Hole(n,_,_) => k -> n }
    
    val res = if (defs isEmpty) r else bottomUp(r) {
      case h @ Hole(n,_,_) => defs get n map (_()) getOrElse h
      case h @ SplicedHole(n,_) => defs get n map (_()) getOrElse h
      case s: Sym =>
        //println("Trav "+s, nameMap get s flatMap (defs get _) map (_()) getOrElse s)
        nameMap get s flatMap defs.get map (_()) getOrElse s
      case r => r
    }
    
    res |> inlineUnlessEnclosedOr(r.isInstanceOf[PardisBlock[_]])  alsoApply (r => debug(s"SUBS RESULT = $r"))
  }
  
  def hole(name: String, typ: TypeRep): Rep = Hole(name, typ, None)
  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep = throw new IRException(s"Unsupported: HOPV")
  def splicedHole(name: String, typ: TypeRep): Rep = SplicedHole(name, typ)
  def typeHole(name: String): TypeRep = TypeHole(name)
  
  
  
  // * --- * --- * --- *  Implementations of `TypingBase` methods  * --- * --- * --- *
  
  
  def uninterpretedType[A: TypeTag]: TypeRep = {
    //println("Unint: "+implicitly[TypeTag[A]])
    implicitly[TypeTag[A]].tpe match {
      case ruh.Any => types.AnyType
      case ruh.Nothing => types.NothingType.asInstanceOf[TypeRep]
      case typ =>
        throw new IRException(s"Unsupported uninterpreted type: `$typ`")
    }
  }
  def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
    // This can happen in some cases, but is usually just a quirk
    null
  }
  def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
    //println(s"Type $typ $targs "+typ.isStatic)
    
    if (typ.isModuleClass) return null
    // ^ sometimes happen that we get `object Seq` (as an arg to CanBuildFrom), not sure why;
    // also when we have `scp.lib.Var`, we get `scp.lib` here -- TODO investigate why
    
    val (obj,tname) = typ.name.toString match {
      case "CanBuildFrom" =>
        val _::arg::coll::Nil = targs
        return CanBuildFromType(coll,arg,coll)
      case _ if targs.nonEmpty && typ === ruh.FunctionType.symbol(targs.size-1) => sc.Predef -> ("typeLambda"+(targs.size-1))
      case _ => sc -> ("type"+typ.name.toString)
    }
    
    try {
      val rec -> m = try obj -> obj.getClass.getMethod(tname, targs map (_ => classOf[TypeRep]): _*)
      catch { case e: NoSuchMethodException =>
        PardisTypeImplicits -> PardisTypeImplicits.getClass.getMethod(tname, targs map (_ => classOf[TypeRep]): _*)
      }
      val r = m.invoke(rec, targs: _*)
      r.asInstanceOf[TypeRep]
    } catch {
      case e: NoSuchMethodException =>
        throw new IRException(s"Could not find a deep type representation for type symbol `$typ` (tried name ${'"'+tname+'"'}); perhaps it is absent from the DSL cake.", Some(e))
    }
    
  }
  def recordType(fields: List[(String, TypeRep)]): TypeRep = ???
  def constType(value: Any, underlying: TypeRep): TypeRep = underlying
  
  // TODO refine? Basic subtyping like Int <: Any? also look out for non-covariance...
  def typLeq(a: TypeRep, b: TypeRep): Boolean =
    (a.name === b.name) && ((a.typeArguments zipAnd b.typeArguments)((typLeq _).asInstanceOf[(TR[_],TR[_])=>Bool]) forall identity)
  
  
  
  // * --- * --- * --- *  Implementations of `IntermediateBase` methods  * --- * --- * --- *
  
  
  def repType(r: Rep): TypeRep = r match {
    case r: PardisVar[_] => r.e.tp
    case r: PardisNode[_] => r.tp
    case r: Stm => r.typeT
    //case r: Hole[_] => r.tp
    // PardisFunArg:
    case r: PardisLambdaDef => ???
    case r: PardisVarArg =>
      // The underlying node of a PardisVarArg is a Seq(...), of Seq[T] type (we just want the T)
      r.underlying.typ.typeArguments.head
    case r: Expr => r.tp
    //case r: Sym => r.tp  // is an Expr
    //case r: Block => r.res.tp  // is a PNode
  }
  def boundValType(bv: BoundVal): TypeRep = bv.tp
  
  def reinterpret(r: Rep, newBase: Base)(extrudedHandle: (BoundVal => newBase.Rep) = DefaultExtrudedHandler): newBase.Rep =
    throw new NotImplementedException
  
  
  
  // * --- * --- * --- *  Implementations of `InspectableBase` methods  * --- * --- * --- *
  
  
  def bottomUp(r: Rep)(f: Rep => Rep): Rep = transformRep(r)(identity, f)
  def topDown(r: Rep)(f: Rep => Rep): Rep = transformRep(r)(f)
  def transformRep(r: Rep)(pre: Rep => Rep, post: Rep => Rep = identity): Rep = (new RepTransformer(pre,post))(r)
  
  // FIXME: probably doesn't work for things other than Block's: have to reify statements again (cf: global symbol map)
  // ^ TODOmaybe simply rebind things in the global map; we don't care about the old value of transformed stuff anyway (Q: is it okay with speculative Rw?)
  class RepTransformer(pre: Rep => Rep, post: Rep => Rep) {
    
    def apply(r: Rep): Rep = /*println(s"Apply: $r") before*/ post(pre(r) match {
    // PardisNode
        
      case b: Block => transformBlock(b)
        
      // Note: we do not try to transform the inputs to lambdas, as there is no Sym=>Sym mapping available
      // Note: no need to renew the symbols, as it should be done by block inlining and reflect(s: Stm)
      case PardisLambda0(f, o: ABlock) =>
        val newBlock = o |> pre |> apply |> post |> toBlock
        PardisLambda0[Any](() => newBlock |> toExpr, newBlock)(o.tp)
      case pl @ PardisLambda(f, i, o: ABlock) =>
        val newBlock = o |> pre |> apply |> post |> toBlock
        PardisLambda[Any,Any](x => bottomUpPartial(newBlock) { case `i` => x } |> toExpr, i, newBlock)(pl.typeT, pl.typeS)
      case pl @ PardisLambda2(f, i0, i1, o: ABlock) =>
        val newBlock = o |> pre |> apply |> post |> toBlock
        PardisLambda2[Any,Any,Any]((x0,x1) => bottomUpPartial(newBlock) { case `i0` => x0 case `i1` => x1 } |> toExpr, i0, i1, newBlock)(pl.typeT1, pl.typeT2, pl.typeS)
      case pl @ PardisLambda3(f, i0, i1, i2, o: ABlock) =>
        val newBlock = o |> pre |> apply |> post |> toBlock
        PardisLambda3[Any,Any,Any,Any]((x0,x1,x2) => bottomUpPartial(newBlock) { case `i0` => x0 case `i1` => x1 case `i2` => x2 } |> toExpr, i0, i1, i2, newBlock)(pl.typeT1, pl.typeT2, pl.typeT3, pl.typeS)
        
      case r: PardisNode[_] => 
        r.rebuild(r.funArgs map transformFunArg: _*)
        
    // PardisFunArg
        
      // Expr
        case cst: pir.Constant[_] => cst
        //case ex: ExpressionSymbol[_] => ex
        case ex: ExpressionSymbol[_] => curSubs.getOrElse(ex, ex)
        //case ex: ExpressionSymbol[_] => ex |> transformSym
        case ah: AnyHole[_] => ah
        
      case PardisVarArg(v) => PardisVarArg(v |> transformFunArg)
      
      // TODO? PardisLambdaDef
        
    }) //and (r => println(s"Result: $r"))
    
    def transformFunArg: PardisFunArg => PardisFunArg = fa => fa |> apply |>=? { case PardisVarArg(v) => v } |> {
      // Q: can it happen that we transform a simple Rep into a Block, where the Block should not exist (since it's not a by-name arg)?
      // Just in case, check that the original node was already a Block, otherwise inline!
      case b: Block =>
        if (fa.isInstanceOf[Block]) b
        else b |> inlineBlock
      case fa: PardisFunArg => fa
      case x => x |> toExpr
    }
    
    def transformBlock(b: Block): ABlock = sc.reifyBlock[Any] {
      def rec(sts: List[Stm]): Unit = sts match {
        case sc.Stm(sym, rhs) :: sts =>
          apply(rhs) match {
            case d: Def[_] =>
              (if (d|>pure) sc._IRReifier.findSymbol(d)(d.tp) else None) getOrElse (sc.Stm(sym, d)(sym.tp) |> reflect)
              // ^ Note: not renewing the symbol (I think it's unnecessary)
              rec(sts)
            case r: Rep =>
              val e = r |> toExpr
              withSubs(sym -> e)(rec(sts))
          }
        case Nil =>
        case _ => spuriousWarning // Scala spurious warning
      }
      rec(b.stmts)
      b.res |> apply |> toExpr
    }(b.tp)
    
  }
  
  protected def failExtrWith(msg: => String) = none alsoDo debug(s"${Console.RED}$msg${Console.RESET}")
  
  override def merge(a: Extract, b: Extract): Option[Extract] =
    super.merge(a,b) |>=? { case None => failExtrWith(s"Cannot merge: $a and $b") }  
  
  
  protected def extract(xtor: Rep, xtee: Rep): Option[Extract] = debug(s"${"Extr." |> bold} $xtor << $xtee") thenReturn nestDbg(xtor -> xtee match {
      
    case Hole(name, typ, _) -> _ =>
      typ extract (xtee.typ, Covariant) flatMap { merge(_, (Map(name -> xtee), Map(), Map())) }
      
    case (Constant(v1), Constant(v2)) =>
      mergeOpt(extractType(xtor.typ, xtee.typ, Covariant),
        if (v1 === v2) Some(EmptyExtract) else failExtrWith(s"Different constant values: $v1 =/= $v2"))
      
    // TODO proper impl of extraction
    case _ -> sc.Block(Nil, r1) => xtor extract r1
    case sc.Block(Nil, r0) -> _ => r0 extract xtee
    case sc.Block(s0, r0) -> sc.Block(s1, r1) => ???
      
    case Def(f0: pir.FunctionNode[_]) -> Def(f1: pir.FunctionNode[_]) if pure(f0) && pure(f1) =>
      extractDef(f0, f1)
      
    case (es0: ExpressionSymbol[_]) -> (es1: ExpressionSymbol[_]) if es0 == es1 => SomeEmptyExtract
    
    case (es0: ExpressionSymbol[_]) -> (es1: ExpressionSymbol[_]) if es1 |>? rwrCtx contains es0 => SomeEmptyExtract // Q: handle xted bindings here?
      
    case (es0: ExpressionSymbol[_]) -> Hole(name, _, Some(s)) if es0 == s => SomeEmptyExtract  // "hole memory"
      
    case PardisVarArg(SplicedHole(name,typ)) -> PardisVarArg(Def(PardisLiftedSeq(seq))) =>
      typ extract (xtee.typ, Covariant) flatMap { merge(_, mkExtract()()(name -> seq)) }
      
    case _ => failExtrWith(s"No match.")
      
  })
  
  protected def extractDef(xtor: Def[_], xtee: Def[_]): Option[Extract] = {
    xtor -> xtee match {
      case (f0: pir.FunctionNode[_], f1: pir.FunctionNode[_]) =>
        if (f0.name =/= f1.name) failExtrWith(s"Different names: ${f0.name} =/= ${f1.name}")
        else for {
          e <- f0.caller -> f1.caller match {
            case Some(c0) -> Some(c1) => c0 extract c1
            case None -> None => SomeEmptyExtract
            case c0 -> c1 => throw IRException(s"Inconsistent callers: $c0 and $c1")
          }
          () = assert(f0.typeParams.size === f1.typeParams.size)
          ts <- mergeAll( (f0.typeParams zip f1.typeParams) map { case (a,b) => weakenTypeRep(a) extract (b, Covariant) } )
          e <- merge(e, ts)
          ass <- mergeAll( (f0.funArgs zipAnd f1.funArgs)(_ extract _) )
          e <- merge(e, ass)
        } yield e
      case (HoleDef(h), _) => extract(h, xtee)
      case (f0: pir.PardisNode[_], f1: pir.PardisNode[_]) =>
        if (f0.nodeName =/= f1.nodeName) failExtrWith(s"Different names: ${f0.nodeName} =/= ${f1.nodeName}")
        else mergeAll( (f0.funArgs zipAnd f1.funArgs)(_ extract _) )
      case (b0: Block, _) => b0 extract xtee
      case (_, b1: Block) => failExtrWith(s"Can't extract a Block with $xtor")
    }
  }
  
  protected def extractBlock(xtor: Block, xtee: Block): Option[Extract] = {
    /*
    //val left = xtor.stmts
    //def rec(ex: Extract, matchedVals: List[Sym])(xy: Block -> Block): Option[Rep] = /*println(s"rec $xy") before*/ (xy match {
    def rec(matchedHoles: List[BoundVal -> List[Stm]])(left: List[Stm], right: List[Stm]): Option[List[BoundVal -> List[Stm]] -> Extract] = left -> right match {
      //case (l :: ls) -> _ if d0(l) |> isHole => rec((l -> Nil) :: matchedHoles)(ls, right)
      //case (l :: ls) -> (r :: rs) => 
      case Nil -> Nil => matchedHoles -> EmptyExtract |> some
      case _ => ???
    }
    rec(Nil)(xtor.stmts, xtee.stmts)
    */
    ???
  }
  
  // TODO proper impl w/ cleanup
  // the xtor symbol a symbol has been matched with
  // extraction should make the corresponding xtor Stm match the Stm
  // substitution should apply based on associated Stm name
  type RwContext = PartialFunction[Sym, Sym]
  //def rwrCtx: RwContext = ???
  val rwrCtx = mutable.Map[Sym, Sym]()
  
  
  def bold(str: String) = {
    import Console.{BOLD, RESET}
    s"${BOLD}$str$RESET"
  }
  
  def pure(d: Def[_]) = d match {
    case d: PardisReadVal[_] => true
    case _ => d isPure
  }
  
  
  def varsIn(r: Rep): Set[Sym] = ???
  
  private def trunc(x: Any) = {
    val str = x.toString
    val s = str.splitSane('\n')
    if (s.size > 5) (s.iterator.take(5) ++ Iterator("... < truncated > ...")) mkString "\n"
    else str
  }
  
  override def rewriteRep(xtor: Rep, xtee: Rep, code: Extract => Option[Rep]): Option[Rep] = /*ANFDebug muteFor*/ {
    debug(s"${"Rewriting" |> bold} ${xtee|>trunc} ${"with" |> bold} $xtor")
    
    xtee |>? {
      case _:Block => // Block is a Def
      case (_:PardisVarArg)|(_:PardisLiftedSeq[_])|(_: Def[_]) =>
        return failExtrWith(s"Can't match that with a block.")
    }
    
    def codeBlock(ex: Extract): Option[Block] = try typedBlock(code(ex) getOrElse (
      return failExtrWith("Rewritten code could not be constructed successfully: returned None"))
    ) |> some alsoApply (c => debug(s"Constructed code: ${c.get|>trunc}")) catch {
      case e: NoSuchElementException if e.getMessage === s"key not found: $SCRUTINEE_KEY" =>
        throw IRException(s"Could not extract a scrutinee for this rewrite pattern: ${xtor |> showRep}")
      case e: Throwable =>
        failExtrWith(s"Rewritten code could not be constructed successfully: threw $e")
        throw e }
    
    type Val = Sym
    type ListBlock = List[AStm] -> Expr
    
    def constructBlock(lb: ListBlock): ABlock = sc.reifyBlock[Any] {
      lb._1 foreach reflect
      lb._2
    }(lb._2.tp)
    
    def toHole(from: Sym, to: Sym): Extract = {
      debug(s"TODO Should bind $from -> $to")
      // TODO handle xted bindings!
      rwrCtx += from -> to // TODO cleanup, make reentrant
      EmptyExtract
    }
    
    /** Tries to apply a RwR on a list of statements by trying to match the xtor (itself a list of statements),
      * then applying the associated `code` function and checking removed statements are not used later on in the list.
      * Note: we accumulate skipped pure statements in `pureStms` because we need to look at them to see if they refer to removed nodes
      * @return pure statements encountered and skipped, rewritten block output by `code`, rest of the statements */
    def rec(ex: Extract, matchedVals: List[Val -> Val], pureStms: List[AStm])(xy: ListBlock -> ListBlock): Option[(List[Stm], Block -> Option[Val], ListBlock)] =
    debug(s"rec ${xy._1}\n<<  ${xy._2._1.headOption filter (_.rhs.isPure) map (_ => "[PURE]") getOrElse "" }${xy._2|>trunc}") thenReturn nestDbg(xy match {
        
      case ((sc.Stm(b0, e0) :: es0) -> r0, ((s1 @ sc.Stm(b1, e1)) :: es1) -> r1) =>
        val trial1 = for {
          e <- extractDef(e0, e1)
          e <- merge(e, ex)
          e <- merge(e,
            if (b0.name endsWith XTED_BINDER_SUFFIX) repExtract(b0.name.dropRight(XTED_BINDER_SUFFIX.length) -> b1)
            else toHole(b1, b0)
          )
          // Try to match the current xtor binding with the corresponding xtee binding, and proceed with the rest
          r <- rec(e, b0 -> b1 :: matchedVals, pureStms)(es0 -> r0, es1 -> r1)
          
        } yield r
        if (trial1.isEmpty && (e1 |> pure) // try ignoring the pure statement if taking it in the match did not work out
          // Note: because of the pattern in this case, we don't allow ignoring statements at the end just before the return
          // – this used to be explicitly implemented as condition `xy._1._1.nonEmpty`
          && matchedVals.nonEmpty // don't want to start skipping defs before the xtion has even begun
        ) rec(ex, matchedVals, s1 :: pureStms)(xy._1, es1 -> r1)
        else trial1 
        
      case (Nil -> r0, bl @ sts -> r1) =>
        
        // Function to check that a set of bound vals are not used in a list of statements,
        // trying to remove pure statements referring to them, and transitively
        def removeStmts(acc: List[AStm])(toRm: Set[Val], from: List[AStm], fromRet: Expr): Option[List[AStm]] = debug(s"To remove: $toRm from $from ret $fromRet") thenReturn from match {
          case st :: stms =>
            val refs = freeVars(st.rhs)
            //debugVisible(s"Free vars $refs in ${st.rhs}")
            if (refs intersect toRm nonEmpty) {
              if (st.rhs |> pure) debug(s"Getting rid of pure ${st.sym}") thenReturn removeStmts(acc)(toRm + st.sym, stms, fromRet)
              else failExtrWith(s"Statement ${st.sym} references symbols in the remove set ${toRm}")
            } else removeStmts(st :: acc)(toRm, stms, fromRet)
          case Nil if fromRet |>? {case s:Sym => toRm(s)} forall (!_) => 
            Some(acc.reverse)
          case Nil => failExtrWith(s"Returned symbol ${fromRet} is in the remove set ${toRm}")
        }
        
        debug(s"Matched $matchedVals; ret $r1")
        debug(s"Skipped Pure $pureStms")
        
        val block = bl |> constructBlock
        
        // In case we're at the end of the xtor block, try to use its result to extrac the whole of the remaining xtee
        // This implements eager matching, which allow things like `case ir" ... ; $body: $t "` to work and extract the full body.
        (for {
          
          e <- extract(r0, block)
          e <- merge(e, ex)
          // The extracted scrutinee is the returned expression – here the whole remaining block:
          e <- merge(e, repExtract(SCRUTINEE_KEY -> block))
          () = debug(s"${Console.GREEN}Constructing bin-rewritten code with $e${Console.RESET}")
          matchedNonExtractedVals = matchedVals.filterNot(_._1.name endsWith XTED_BINDER_SUFFIX)
          bindings = matchedNonExtractedVals collect {
            case a -> b if a.name contains NAME_SUFFIX =>
              b -> Hole(a.name splitAt (a.name indexOf NAME_SUFFIX) _1, b.tp, Some(b))
          }
          //() = debug("Bindings: "+bindings)
          b <- withSubs(bindings:_*) {codeBlock(e)} // TODO do that in other cases too!
          
          //pureStmsR = pureStms.reverse  // makes typechecking fail with arcane error...
          _ <- removeStmts(Nil)(matchedNonExtractedVals.unzip._2.toSet, pureStms/*.reverse*/ ++ b.stmts.asInstanceOf[List[AStm]], b.res)
          newPureStms <- removeStmts(Nil)(matchedNonExtractedVals.unzip._2.toSet, pureStms.reverse, b.res)
          // ^ Note: `pureStms` passed here are not correctly ordered and may refer to things bound later,
          // but they'll be ignored and only reintroduced if necessary at the end of the rewriteRep algo (TODO)
          
        } yield (newPureStms, b -> (r1 |>? {case s: Sym => s}), Nil -> b.res)
          //                                                    ^ Nil here because the entire end of the block was matched
        ) orElse { if (r0 |> isHole || matchedVals.isEmpty) None else { // If we're not in a $body-result xtor – we're not going to match the result, so it would be unsound if it had a hole
          // If the above did not work, try only matching statements up to where we are currently in the xtee
          // This implements sequential statements rewriting, which can operate in the middle of blocks
          
          val matchedRet = matchedVals find (_._1 == r0) map (_._2)
          //val matchedRet = matchedVals collect { case `r0`->bv => bv }  // Crashes Scalac!!
          
          debug(s"Matched $matchedVals; ret $r1")
          debug(s"MatchedRet $matchedRet")
          
          val r = for {
            newStms <- removeStmts(Nil)(matchedVals.unzip._2.toSet -- matchedRet, pureStms ++ sts, r1)
            // ^ Note: `pureStms` passed here are not correctly ordered and may refer to things bound later,
            // but they'll be ignored and only reintroduced if necessary at the end of the rewriteRep algo
            newPureStms <- removeStmts(Nil)(matchedVals.unzip._2.toSet -- matchedRet, pureStms.reverse, r1)
            // The extracted scrutinee is the returned expression, or the last matched symbol if there are none:
            e <- matchedRet orElse (matchedVals.headOption map (_._2)) map (mr => merge(ex, repExtract(SCRUTINEE_KEY -> mr))) getOrElse some(ex)
            () = debug(s"${Console.GREEN}About to construct seq-rewritten code with ${e|>trunc}${Console.RESET}")
            bloc <- codeBlock(e)
          } yield (newPureStms, bloc -> matchedRet, newStms -> r1)
          
          debug("Maybe rewrote sequence to "+r)
          
          r
          
        }}
        
      case _ =>
        debug("Rec reached default case")
        None
        
    })
    
    def toBlock(x: Rep): Bool -> ListBlock = x match {
      case sc.Block(sts:List[AStm @unchecked], r) => true -> (sts -> r)
      case r: Expr => false -> (Nil -> r)
      // This is probably a bad idea (used to be enabled):
      //case d: Def[_] => val f = sc.fresh(d.tp); false -> ((sc.Stm[Any](f,d)(f.tp)::Nil) -> f)
    }
    
    def process(xtor: ListBlock, xtee: ListBlock): List[Stm \/ (Block -> Option[Val])] = {
      rec(EmptyExtract, Nil, Nil)(xtor, xtee) match {
        case Some((ps, b -> v, lb)) => 
          //debugVisible(ps)
          //Right(b -> v) +: process(xtor, lb)
          // FIXME: not really correct to use `ps` here:
          ((ps map Left.apply) :+ Right(b -> v)) ++ (
            if (lb._1.nonEmpty) process(xtor, lb)
            else Nil // in case we have not matched any statement, don't recurse as it could lead to an infinite loop
          )
        case None => xtee match {
          case (st :: sts) -> r => Left(st) :: process(xtor, sts -> r)  // Note: no need to pass around the return?
          case Nil -> r => Nil
        }
      }
    }
    val (xteeWasBlock, xteeBlock) = xtee |> toBlock
    val processed = process(xtor |> toBlock _2, xteeBlock)
    
    
    if (processed forall (_ isLeft)) none  // No RwR have kicked in
    else {
      
      val sub = mutable.Map[Val,Rep]()
      def addBinding(ft: Val -> Rep) = {  // lol, changing Rep to Expr crashes Scalac
        sub += ft
        // Support for transitivity:  (Q: really needed?)
        for (f -> ft._1 <- sub; ft._2 -> t2 <- sub if t2 =/= ft._2) sub += f -> t2
      }
      
      val b = sc.reifyBlock[Any] {
        // TODO reintroduce pure stmts
        processed foreach {
          case Left(s: Stm) => reflect(s)
          case Right(bl -> v) =>
            v foreach (_ -> bl.res |> addBinding)
            //debug(s"Inlining with substitutions $sub, block: $bl")
            bl.stmts foreach reflect
        }
        /*
        // If the last segment is a rewritten block and it does not have a matched val result (it could be e.g. a constant),
        // use this as the result of the whole thing
        processed.lastOption collect { case Right(bl -> None) => assert(!xteeBlock._2.isInstanceOf[ExpressionSymbol[_]]); bl.res } getOrElse xteeBlock._2
        */
        // If the result of the xtee is a Sym, it will be according to the rewritings that have taken place.
        // Otherwise (it could be e.g. a constant), it could have been rewritten and have produced a block in the last
        // `processed` segment, so we check for it.
        xteeBlock._2 |>? { case s: Sym => s } orElse (processed.lastOption collect { case Right(bl -> None) => bl.res }) getOrElse xteeBlock._2
        
      }(xtee.typ)
      
      //debug(s"Mapping: $sub")
      //debug(s"Pre: $b")
      
      // Update all the references to rewritten statements blocks:
      val b2 = bottomUpPartial(b){ case s:Sym => sub.getOrElse(s, s) }
      
      //debug(s"Post: $b2")
      
      // Not sure really useful to make a distinction here; used to always wrap (then it'd get inlined later anyways)
      val r = if (xteeWasBlock) b2
        else b2 |> toExpr // to inline the Block if necessary
      
      //debug(s"Res: $r")
      
      r
      
    } |> some alsoApply (r => debug(s"${"Rewrote:" |> bold} ${r|>trunc}"))
    
  }
  
  
  
  protected def spliceExtract(xtor: Rep, t: Args): Option[Extract] = ???

  // TODO refine? Basic subtyping like Int <: Any?
  def extractType(xtor: TypeRep, xtee: TypeRep, va: Variance): Option[Extract] = debug(s"$va ${s"TypExtr." |> bold} $xtor << $xtee") thenReturn nestDbg(xtor match {
    case TypeHole(name) => mkExtract()(name -> xtee)() |> some
    case _ =>
      val xtorNameBase = xtor |> baseName
      val xteeNameBase = xtee |> baseName
      if (xtorNameBase =/= xteeNameBase) failExtrWith(s"Different type names: ${xtorNameBase} =/= ${xteeNameBase}")
      else {
        assert(xtor.typeArguments.size === xtee.typeArguments.size)
        mergeAll((xtor.typeArguments zipAnd xtee.typeArguments)(extractType(_,_,va))) // TODO proper handling of va
      }
  })
  protected def baseName(tp: TypeRep) = (tp:TR[_]) match {
    case _: types.Lambda0Type[_] => "Function0"
    case _: types.Lambda1Type[_,_] => "Function1"
    case _: types.Lambda2Type[_,_,_] => "Function2"
    case _: types.Lambda3Type[_,_,_,_] => "Function3"
    case _ => tp.name takeWhile (_ =/= '[')
  }
  
  
  /** Extraction nodes need to be wrapped in a Block, because it makes no sense to let statements escape the pattern. */
  override def wrapExtract(r: => Rep): Rep = typedBlock(r)
  /** In case there is no enclosing block, just create one instead of crashing!
    * If the resulting Block node is inserted as an expression later in a tree, it will be inlined anyway. */
  override def wrapConstruct(r: => Rep): Rep =
    if (sc._IRReifier.scopeDepth == 0) typedBlock(r)
    else r |> toExpr  // inlines blocks and calls toAtom on Def's
  
  
  
  
  // * --- * --- * --- *  Other Implementations * --- * --- * --- *
  
  
  protected def traversePartial(f: PartialFunction[Rep, Boolean]) = traverse(f orElse PartialFunction(_ => true)) _
  
  protected def traverse(f: Rep => Boolean)(r: Rep): Unit = {
    val continue = f(r)
    val rec = if (continue) traverse(f) _ else ignore
    r match {
    // PardisNode
        
      case b: Block => if (continue) b.stmts foreach rec thenReturn b.res |> rec
        
      case sc.Stm(s, o) => o |> rec
        
      case PardisLambda0(f, o: ABlock) => o |> rec
      case PardisLambda(f, i, o: ABlock) => o |> rec
      case PardisLambda2(f, i0, i1, o: ABlock) => o |> rec
      case PardisLambda3(f, i0, i1, i2, o: ABlock) => o |> rec
        
      case r: PardisNode[_] => if (continue) r.funArgs foreach rec
        
    // PardisFunArg
        
      // Expr
        case cst: pir.Constant[_] =>
        case ex: ExpressionSymbol[_] =>
        case ah: AnyHole[_] =>
        
      case PardisVarArg(und) => und |> rec
        
      // TODO? PardisLambdaDef
        
    }
  }
  
  protected def freeVars(r: Rep): collection.Set[BoundVal] = {
    // FIXME Q: can there ever be the same sym bound several times? (cf block inlining)
    val referenced = mutable.Set[BoundVal]()
    val bound = mutable.Set[BoundVal]()
    r |> traversePartial {
      case s: Sym => referenced += s; true
      case sc.Stm(s,rhs) => bound += s; true
      case PardisLambda(f, i: ASym @unchecked, o: ABlock) => bound += i; true
      case PardisLambda2(f, i0: ASym @unchecked, i1: ASym @unchecked, o: ABlock) => bound += i0; bound += i1; true
      case PardisLambda3(f, i0: ASym @unchecked, i1: ASym @unchecked, i2: ASym @unchecked, o: ABlock) => bound += i0; bound += i1; bound += i2; true
    }
    referenced -- bound
  }
  
  
  protected def isHole(r: R[Any]) = r |>? { case Hole(_,_,_)|SplicedHole(_,_) => } isDefined
  
  def block[T:CodeType,C](q: => Code[T,C]) = `internal Code`[T,C](pardisBlock[T,C](q))
  def pardisBlock[T:CodeType,C](q: => Code[T,C]) = sc.reifyBlock[T] { toExpr(q.rep).asInstanceOf[R[T]] }
  
  
  implicit def typeRepFromCodeType[A:CodeType]: sc.TypeRep[A] = implicitly[CodeType[A]].rep.asInstanceOf[sc.TypeRep[A]]
  
  implicit def weakenTypeRep(tr: TR[_]): TypeRep = tr.asInstanceOf[TypeRep]
  
  
}



