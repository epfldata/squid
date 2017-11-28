package example

import squid._
import utils._
import ir._
import utils.Debug.show

/**
  * Created by lptk on 15/09/16.
  * 
  * Assumptions:
  *   Variables not initialized with null are assumed never to contain null. (arbitrary)
  *     So if you intend for a variable to be assignable to null, instead of writing `var a = init`, write `var a: T = null; a = init`
  *     Note: could instead use @Nullable annotation... (cleaner approach)
  * 
  */
trait TupleVarOptim extends SimpleRuleBasedTransformer { self =>
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  import squid.lib.Var
  
  rewrite {
    
    case code"val $tup = Var($init: ($ta, $tb)); $body: $t" =>
      //println((ta,tb)) // makes the rwr not compile -- FIXME
      //println(ta->tb) // makes the rwr not compile
      
      //show(body)
      
      val a = code"a? : Var[$ta]"
      val b = code"b? : Var[$tb]"
      
      val isInitializedWithNull = init =~= code"null"  // TODO more precise?
      
      if (isInitializedWithNull) {
        
        val isNull = code"isNull? : Var[Bool]"
        var hasNull = isInitializedWithNull
        
        val body2 = body rewrite {
          case code"($$tup !)._1" => code"assert(!$isNull.!); $a !"
          case code"($$tup !)._2" => code"assert(!$isNull.!); $b !"
            
          case code"($$tup !) == null" => ??? // ir"$isNull.!"
          // ^ For some reason, this (and other variants) never seems to match! Only the following does:
          case code"($x:Any) == null" if x =~= code"v? : ($ta,$tb)" => code"$isNull.!"
            
          case code"$$tup := ($va: $$ta, $vb: $$tb)" => code"$a := $va; $b := $vb; $isNull := false"
          case code"$$tup := $vab" => code"val n = $vab == null; if (!n) { $a := $vab._1; $b := $vab._2; $isNull := n }"
          case code"$$tup := null" => code"$isNull := true"
          case code"$$tup !" => code"($a.!, $b.!)"
        }
        
        val body3 = body2 subs 'tup -> {
          throw RewriteAbort(s"tup is still used! in: $body2")}
        code" val isNull = Var(${Const(isInitializedWithNull)}); val a = Var(${nullValue[ta.Typ]});  val b = Var(${nullValue[tb.Typ]});  $body3 "
        
      } else {
          
        val body2 = body rewrite {
          case code"($$tup !)._1" => code"$a !"
          case code"($$tup !)._2" => code"$b !"
          case code"$$tup := ($va: $$ta, $vb: $$tb)" => code"$a := $va; $b := $vb"
          case code"$$tup := $vab" => code"$a := $vab._1; $b := $vab._2"
          case code"$$tup := null" => ???; code"???" // FIXME proper error
          case code"$$tup !" => code"($a.!, $b.!)"
        }
        
        //show(body2)
        
        val body3 = body2 subs 'tup -> {
          //println(s"tup is still used! in: ${newBody rep}")
          throw RewriteAbort(s"tup is still used! in: $body2")}
        
        code" val init = $init; val a = Var(init._1);  val b = Var(init._2);  $body3 "
        
      }
      
      
    // Note: this should be moved to another class; it is useless when tuple ops are viewed by ANF as trivial (then one wants TupleNormalization instead)
    case code"val $tup = ($a: $ta, $b: $tb); $body: $t" => // assume ANF, so that a/b are trivial
      
      val newBody = body rewrite {
        case code"$$tup._1" => code"$a"
        case code"$$tup._2" => code"$b"
        case code"$$tup == null" => code"false"
      }
      //val newwBody2 = newBody subs 'tup -> ir"($a,$b)"  // can't do that as otherwise the transformer would have no fixed point
      val newwBody2 = newBody subs 'tup -> (throw RewriteAbort())
      newwBody2
    
  }
  
}


object TupleVarOptimTests extends App {
  object DSL extends SimpleAST
  import DSL.Predef._
  import DSL.Quasicodes._
  
  object Optim extends DSL.SelfTransformer with TupleVarOptim with TopDownTransformer
  
  var pgrm = ir{
    var t = (readInt, readInt)
    if (t._1 > t._2) t = (t._2, t._1)
    t._1 to t._2
  }
  
  show(pgrm)
  
  pgrm = pgrm transformWith Optim
  show(pgrm)
  
  //show(pgrm.run)
  
  
}


object TupleVarOptimTestsANF extends App {
  object DSL extends SimpleANF
  import DSL.Predef._
  import DSL.Quasicodes._
  
  object Optim extends DSL.SelfTransformer with TupleVarOptim with TopDownTransformer
  
  var pgrm = ir{
    var t = (readInt, readInt)
    if (t._1 > t._2) t = (t._2, t._1)
    t._1 to t._2
  }
  
  //show(pgrm rep)
  show(pgrm)
  
  pgrm = pgrm transformWith Optim
  
  //show(pgrm rep)
  show(pgrm)
  
  //show(pgrm.run)
  
  
}




