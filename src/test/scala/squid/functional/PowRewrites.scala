package squid
package functional

import utils.GenHelper

class PowRewrites extends MyFunSuite {
  import DSL.Predef._

  val d = code".5"

  val e0 = code"Math.pow($d, 0)".rep -> code"1.0".rep
  val e1 = code"Math.pow($d, 1)".rep -> code"1.0 * $d".rep
  val e2 = code"Math.pow($d, 2)".rep -> code"1.0 * $d * $d".rep
  val e3 = code"Math.pow($d, 3)".rep -> code"1.0 * $d * $d * $d".rep
  
  val p0 = code"println(Math.pow($d, 2) + 1)".rep -> code"println((1.0 * $d * $d) + 1)".rep
  
  
  test("Pow 2") {
    
    object Trans extends ir.SimpleRuleBasedTransformer with ir.TopDownTransformer {
      val base: TestDSL.type = TestDSL
      
      rewrite {
        case code"Math.pow($x, 2)" => code"1.0 * $x * $x" // add `1.0 *` to reuse the same examples as for "Pow n"
      }
      
      assertCompiles(""" rewrite { case code"Math.pow($x, 2)" => ??? } """) // Now we also accept Nothing as the result type
      
      assertDoesNotCompile(""" rewrite { case _ => code"42" } """) // Error:(31, 22) Could not determine extracted type for that case.
      
    }
    
    eqt( Trans.transform(e2._1) , e2._2 )
    eqt( Trans transformBottomUp e2._1 , e2._2 )
    eqt( Trans transformBottomUp p0._1 , p0._2 )
    //eqt( p0._1 bottomUpTransform Trans , p0._2 )
    
  }
  
  test("Pow n") {
    
    object Trans extends ir.SimpleRuleBasedTransformer with ir.TopDownTransformer { val base: TestDSL.type = TestDSL; rewrite {
      
      // Maybe we could make this work with a special-case in the rewrite rule macro
      /*
      // Error:(50, 57) Cannot rewrite a term of context [Unknown Context] to an unrelated context ctx
      case ir"Math.pow(${x: Q[Double,ctx]}, ${Const(n)})" if n.isValidInt && (0 to 32 contains n.toInt) =>
        (1 to n.toInt).foldLeft(ir"1.0": Q[Double,ctx]){ case (acc, n) => ir"$acc * $x" }
      */
      
      // Simplest workaround:
      case code"Math.pow($x, ${Const(n)})" if n.isValidInt && (0 to 32 contains n.toInt) =>
        (1 to n.toInt).foldLeft(code"1.0" withContextOf x){ case (acc, _) => code"$acc * $x" }
        
    }}
    
    eqt( Trans.transform(e0._1) , e0._2 )
    eqt( Trans.transform(e1._1) , e1._2 )
    eqt( Trans.transform(e2._1) , e2._2 )
    eqt( Trans.transform(e3._1) , e3._2 )
    eqt( Trans transformBottomUp p0._1 , p0._2 )
    
  }
  
  
}







