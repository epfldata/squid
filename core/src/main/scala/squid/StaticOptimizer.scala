// Copyright 2019 EPFL DATA Lab (data.epfl.ch)
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

import utils._
import utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.{srum, sru}
import utils.MacroUtils.{MacroSetting, MacroDebug, MacroDebugger}
import lang._
import quasi._
import squid.lang.Optimizer

import scala.language.experimental.macros
import scala.annotation.{StaticAnnotation, compileTimeOnly}

case class DumpFolder(folderName: String)

/** This is used to optimize snippets of Scala code at runtime by enclosing them within an `optimize{...}` block */
class StaticOptimizer[Optim <: Optimizer] {
  
  def optimize[A](code: A): A = macro StaticOptimizerMacros.optimizeImpl[Optim]
  @MacroSetting(debug = true) def dbg_optimize[A](code: A): A = macro StaticOptimizerMacros.optimizeImpl[Optim]
  
  def optimizeAs[A](name:Symbol)(code: A): A = macro StaticOptimizerMacros.optimizeAsImpl[Optim]
  @MacroSetting(debug = true) def dbg_optimizeAs[A](name:Symbol)(code: A): A = macro StaticOptimizerMacros.optimizeAsImpl[Optim]
  
}

/** TODO generate a macro that lifts passed arguments and compiles the body (caching/or inlining) -- like a static staging */
@compileTimeOnly("Enable macro paradise to expand macro annotations.")
class template(stopt: StaticOptimizer[_]) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro ???
}

@compileTimeOnly("Enable macro paradise to expand macro annotations.")
class optimize(stopt: StaticOptimizer[_]) extends StaticAnnotation {
//class optimize(implicit squid: Squid[_]) extends StaticAnnotation { // Cannot get it to work properly
  //def macroTransform(annottees: Any*): Any = macro StaticOptimizerMacros.optimizeAnnotImpl[Trans] // implementation restriction: macro annotation impls cannot have typetag context bounds (consider taking apart c.macroApplication and manually calling c.typecheck on the type arguments)
  def macroTransform(annottees: Any*): Any = macro StaticOptimizerMacros.optimizeAnnotImpl
}

import scala.reflect.macros.whitebox
import scala.reflect.macros.blackbox

//class StaticOptimizerMacros(override val c: blackbox.Context) extends QuasiBlackboxMacros(c) {
class StaticOptimizerMacros(override val c: whitebox.Context) extends statics.CompileTimeMacros(c) {
  /* ^ Note: using whitebox Context because CompileTimeMacros does, but maybe it would also work with blackbox (perhaps
   *         with a cast), although CompileTimeMacros itself seems to not always work when using blackbox... */
  
  import c.universe._
  
  
  def optimizeAnnotImpl(annottees: Tree*) = {
    
    val stopt = c.macroApplication match {
      case q"new optimize($stopt).macroTransform(..$_)" => stopt
      //case q"new optimize().macroTransform(..$_)" =>
      //  q"_root_.scala.Predef.implicitly[StaticOptimizer[_]]"
      //  //val impt = c.inferImplicitValue(typeOf[Squid[_]]) // <empty>
    }
    
    annottees match {
      case DefDef(mods, name, tparams, vparamss, tpt, rhs) :: Nil =>
        DefDef(mods, name, tparams, vparamss, tpt, q"$stopt.optimize { $rhs }")
    }
  }
  
  
  def optimizeAsImpl[Comp: WeakTypeTag](name: Tree)(code: Tree) = optimizeImpl(code)
  
  def optimizeImpl[Comp: WeakTypeTag](code: Tree) = {
    
    
    val name = c.macroApplication |> {
      case q"$_.optimize[$_]($_)" => None
      case q"$_.dbg_optimize[$_]($_)" => None
      case q"$_.optimizeAs[$_]($t)($_)" => Some(t)
      case q"$_.dbg_optimizeAs[$_]($t)($_)" => Some(t)
    } map {
      case q"scala.Symbol.apply(${Literal(Constant(str:String))})" => str
      case t => c.abort(t.pos, "Name is not a literal.")
    }
    
    
    val Optim = {
      val Comp = weakTypeOf[Comp].widen
      def req(cond: Boolean, msg: => String, dieNow: Boolean = false) =
        if (!cond) {
          val str = s"Type parameter `$Comp` that was passed to StaticOptimizer could not be instantiated without parameters: "+msg
          if (dieNow) c abort (c enclosingPosition, str) else c error (c enclosingPosition, str)
        }
      req(!Comp.asInstanceOf[scala.reflect.internal.Types#Type].isErroneous, "It is erroneous.", true)
      val inst = try {
        val cls = {
          val sym = Comp.typeSymbol
          req(sym.isStatic, "It is not static.")
          req(sym.isClass && !sym.isModuleClass && (Comp match {case RefinedType(_,_) => false case TypeRef(_,_,_)=>true case _ => false}), "It is not a class.", true)
          srum.runtimeClass(srum.staticClass(sym.fullName))
        }
        cls.getConstructors.head.newInstance()
      }
      catch {
        case e: ClassNotFoundException =>
          c.error (c.enclosingPosition, s"Could not find the class of type parameter `$Comp` passed to StaticOptimizer. Perhaps you passed a class defined in the same project. ($e)")
        case e: Throwable =>
          req(false, e.toString)
          throw e
      }
      try inst.asInstanceOf[Optimizer]
      catch {
        case e: ClassCastException => c.abort(c.enclosingPosition, s"Type parameter `$Comp` passed to StaticOptimizer does not conform: "+e)
      }
    }; Optim.wrapOptim(c.enclosingPosition.source.path) {
    
    val Base: Optim.base.type = Optim.base
    
    val varRefs = collection.mutable.Buffer[(String, Tree)]()
    
    val thisNames = collection.mutable.Set[Name]()
    
    object ME extends ModularEmbedding[c.universe.type, Base.type](c.universe, Base, str => debug(str)) {
      import base._
      
      override def liftTerm(x: Tree, parent: Tree, expectedType: Option[Type], inVarargsPos: Boolean = false)(implicit ctx: Map[TermSymbol, BoundVal]): Rep = x match {
        case Select(This(typName),fieldName) 
          if x.symbol != null 
          && (x.symbol.isParameter || x.symbol.isMethod || x.symbol.isPrivateThis) // otherwise we capture things like `scala.collection.immutable`
        /* ^ we make a special case for `isPrivateThis` because it is the only case (I know of) where a class field will 
            not have `isMethod` return true... that's still a heuristic (what if non-fields/parameters are PrivateThis?) */
        /*  The solution above (a case guarded by ad-hoc conditions) is not relly satisfying. 
            We're going to capture method references that may have a static path to them and would be better with a static access.
            Ideally we'd check whether there is a static (and accessible from reflection) path first in the guard of the case.
            OTOH, does it really happen to have a static path to a local method, that will be accessible via the QQ's relfection?
            Note: `!x.symbol.isPackage` is not enough, as then we end up with things like the `List` of `scala.immutable.List` */
        =>
          //val thisName = s"$typName:this:$fieldName"
          val thisName = s"$typName.this.$fieldName"
          thisNames += TermName(thisName)
          base.hole(thisName, liftType(x.tpe))
        case _ => super.liftTerm(x,parent,expectedType,inVarargsPos)
      }
      
      override def unknownFeatureFallback(x: Tree, parent: Tree) = x match {
          
        case Ident(TermName(name)) =>
          varRefs += name -> x
          base.hole(name, liftType(x.tpe))  // FIXME is it safe to introduce holes with such names?
          
        case _ =>
          super.unknownFeatureFallback(x, parent)
          
      }
      
    }
    
    var newCode = wrapSymbolLoadingErrors(Base, ME(code))
    
    debug("Code: "+Base.showRep(newCode))
    
    val pos = c.enclosingPosition
    
    val dumpFolder = resolveCompileTimeImplicit[DumpFolder]("the 'optimize' macro")
    debug(s"Dumping folder: $dumpFolder")
    
    dumpFolder foreach { dumpFolder => 
      val ctx = s"${dumpFolder.folderName}/Gen.${pos.source.file.name.takeWhile(_ != '.')}.${name getOrElse pos.line}.scala"
      Optim.setContext(ctx)
    }
    
    newCode = Optim.optimizeOffline(newCode)
    
    debug("Optimized Code: "+Base.showRep(newCode))
    
    object MBM extends MetaBases {
      val u: c.universe.type = c.universe
      def freshName(hint: String) = c.freshName(TermName(hint))
      /** See similar definition in IntermediateBase. */
      override val runtimeSymbols = Base match {
        case rs: squid.ir.RuntimeSymbols => rs
        case _ => super.runtimeSymbols
      }
    }
    val MB = new MBM.ScalaReflectionBase
    
    //val res = Optim.base.scalaTreeIn(MBM)(MB, newCode)
    //val res = Optim.base.scalaTreeInWTFScala[MBM.type](MBM)(MB, newCode)
    val res = {
      val r = Optim.base.scalaTreeInWTFScala[MBM.type](MBM)(MB, newCode)
      new Transformer { // replacing the names introduced for X.this.y trees
        override def transform(x: Tree) = x match {
          case Ident(name) if thisNames(name) =>
            //val Seq(typ,ths,field) = name.toString.splitSane(':')
            val collection.Seq(typ,ths,field) = name.toString.splitSane('.')
            Select(This(TypeName(typ)),TermName(field))
          case _ => super.transform(x)
        }
      } transform r
    }
    
    // This works but is unnecessary, as currently holes in ScalaReflectionBase are just converted to identifiers
    //res = MB.substitute(res, varRefs.toMap)
    
    debug("Generated: ", showCode(res))
    
    /** The Scala compiler used to crash with a StackOverflow at scala.tools.nsc.Global$Run.compiles(Global.scala:1402)!!
      * unless we used c.parse & showCode. It seems this was because we were splicing symbols directly into QQs */
    res: Tree
    //c.untypecheck(res)
    //c.parse(showCode(res))
  }}
  
  
}
