package squid
package anf

import ir._
import squid.anf.analysis.ControlFlowBase
import squid.anf.analysis.BinOpBase

object BinaryOpsTests {

  object DSL extends SimpleANF with BinOpBase

}
/**
  * Created by lptk on 05/02/17.
  */
class BinaryOpsTests extends MyFunSuite(BinaryOpsTests.DSL) {
  import DSL.Predef._
  import base.{BinOp,Operands,BinOp3}
  
  test("Commuting") {
    
    def f(q:Code[_,{}]) = q rewrite {
      
      // FIXME allow pattern aliases in RwR
      //case ir"${BinOp(bo @ Operands(lhs,rhs))}:$t" => println(lhs,rhs); ???
      case code"${BinOp3(bo0,bo1)}:$t" => 
        ??? // Cannot yet match; see below, for ir"1 + readInt + 1"
        
      //case ir"${BinOp(lhs,rhs)}:$t" =>
      case code"${BinOp(bo)}:$t" if bo.commutes =>
        //println(bo)
        //bo.commute
        Return(bo.commute) // Explicit return so it never re-commutes the result (if the result produces new statements, as in calls to toInt)
        
    }
    
    code"println(readInt+1)" |> f eqt code"println(1+readInt)"
    
    code"readInt-1" |> f eqt code"val ri = readInt; 1.unary_- + ri" // weird, `(-1)+ri` is not accepted as equivalent... 
    
    code"println(readInt + (1:Short))" |> f eqt code"val ri = readInt; println((1:Short).toInt + ri)"
    
    // TODO effect system allowing this one to match (addition is currently let-bound, preventing extraction of the lhs as a BinOp)
    //println(ir"1 + readInt + 1" |> f)
    
  }
  
  
}
