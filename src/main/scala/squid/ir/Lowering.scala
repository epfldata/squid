package squid
package ir

import squid.utils.meta.RuntimeUniverseHelpers
import utils._

trait Lowering extends Transformer {
  val base: ir.AST with ClassEmbedder
  import base._
  
  val warnRecursiveEmbedding = true
  
  val loweredPhases: Set[Symbol]
  
  import ClassEmbedder.Error._
  def transform(rep: Rep): Rep = rep match {
    case RepDef(ma @ MethodApp(self, sym, targs, argss, retTyp)) if ma.phase exists loweredPhases =>
      val fullArgss = if (sym.owner.isModuleClass) argss
        else Args(self)::argss
      val fullTargs = self.typ.tpe.typeArgs.map(new TypeRep(_)) ++ targs // FIXME should use `baseType`! the type of `self` could be a subtype with different type arguments...
      //println(s"Getting $sym in ${self.typ.tpe} fullTargs $fullTargs")
      methodDef(sym, fullTargs) match {
        case Right(Code(r)) =>
          //println(s"Lowering $ma with ${r|>showRep}")
          val res = fullArgss.foldLeft(r) {
            case (r, Args(reps @ _*)) =>
              val ruh = RuntimeUniverseHelpers
              val typ = r.typ.typeArgs.last // TODO be careful that a method implemented without parameter list can implement a method with an empty list (eg toString), which can make this crash
              base.rep(MethodApp(r, ruh.FunctionType.symbol(reps.size).toType member ruh.sru.TermName("apply") asMethod, Nil, Args(reps:_*)::Nil, typ))
            case (r, args) => lastWords(s"Not supported yet: vararg $args") // TODO
          }
          ascribe(res, retTyp) // We ascribe so that if the body is, e.g., `???`, we don't end up with ill-typed code. 
        case Left(Recursive) =>
          if (warnRecursiveEmbedding) System.err.println(s"Warning: Recursive value ${sym fullName} cannot be fully embedded.")
          rep
        case Left(Missing) =>
          System.err.println(s"Warning: Could not find definition for lowered method: ${sym fullName}${sym typeSignature} @ phase ${ma.phase get}") // TODO B/W
          rep
        case _ => spuriousWarning
      }
    case _ => rep
  }
  
}
trait OnlineDesugaring extends OnlineOptimizer with Lowering with ClassEmbedder { self: ir.AST with ClassEmbedder =>
  val loweredPhases = Set('Sugar)
}
