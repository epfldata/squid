package squid
package ir

import utils._
import utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.sru
import squid.lang.InspectableBase

/** Encodes multi-parameter lambdas as curried functions and calls to `uncurry` */
trait CurryEncoding extends InspectableBase { 
  
  def abs(param: BoundVal, body: => Rep): Rep
  def lambdaType(paramTyps: List[TypeRep], ret: TypeRep): TypeRep
  
  def lambda(params: List[BoundVal], bodyThunk: => Rep): Rep = {
    
    lazy val body = bodyThunk // Don't evaluate this too early to preserve execution order!
    
    params match {
        
      //case Nil => import Predef._; `internal IR`(body).erase match { case ir"$body: $t" => ir"scp.lib.asFunction0($body)".rep }
        /* ^ Works, but that case is now handled in the default case */
        
      case p :: Nil => abs(p, body)
        
      case _ =>
        
        val curried = if (params isEmpty) byName(body)
          else (params foldRight (() => body)){ case (p, acc) => () => abs(p, acc()) }()
        
        val typ = lambdaType(params map boundValType, repType(body))
        
        val arity = params.size
        if (arity > 5) throw IRException(s"Unsupported lambda arity: $arity (no associated `uncurried` function)")
        
        val mtd = loadMtdSymbol(loadTypSymbol(ruh.encodedTypeSymbol(sru.typeOf[squid.lib.`package`.type].typeSymbol.asType)), s"uncurried$arity", None)
        
        methodApp(staticModule("squid.lib.package"), mtd, (params map boundValType) :+ body.typ, Args(curried) :: Nil, typ)
        
    }
  }
  
}
object CurryEncoding {
  trait ApplicationNormalizer extends SimpleRuleBasedTransformer {
    import base.Predef._
    
    import lib._
    
    rewrite {
      
      // TODO separate these RW from the actual bond-norm (which ANF does not use -- it may even be harmful to it)
      /** Curries function applications, useful when inlining Scala methods with multiple parameters as lambdas. */
      case code"uncurried0($f: $t)()"                                                        => code"$f"
      case code"uncurried2($f: ($ta => $tb => $t))($x, $y)"                                  => code"$f($x)($y)"
      case code"uncurried3($f: ($ta => $tb => $tc => $t))($x, $y, $z)"                       => code"$f($x)($y)($z)"
      case code"uncurried4($f: ($ta => $tb => $tc => $td => $t))($x, $y, $z, $u)"            => code"$f($x)($y)($z)($u)"
      case code"uncurried5($f: ($ta => $tb => $tc => $td => $te => $t))($x, $y, $z, $u, $v)" => code"$f($x)($y)($z)($u)($v)"
        
    }
    
  }
}
