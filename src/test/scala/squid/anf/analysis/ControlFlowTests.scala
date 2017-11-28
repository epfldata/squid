package squid
package anf

import ir._
import squid.anf.analysis.ControlFlowBase
import squid.anf.analysis.BinOpBase

object ControlFlowTests {
  
  object DSL extends SimpleANF with ControlFlowBase
  
}
/**
  * Created by lptk on 05/02/17.
  */
class ControlFlowTests extends MyFunSuite(ControlFlowTests.DSL) {
  import DSL.Predef._
  import base.{OneOf}
  
  test("OneOf") {
    
    def f(q:Code[_,{}]) = q rewrite {
      //case base.OneOf(oo) =>  // Error:(23, 12) Could not determine extracted type for that case.
      case code"${OneOf(oo)}:$t" =>
        //println(oo)
        
        val a = oo.alt rewrite {
          case code"${Const(n)}:Int" => Const(n+1)
        }
        val _ : Code[t.Typ,oo.C1] = a
        
        oo.rebuild(oo.main, a)
        //oo.rebuild(oo.main, a.asInstanceOf[IR[t.Typ,Any]]) // used to be necessary, cf. RwR path-dep type problems
        
    }
    
    code"println(if (readInt>0) 1 else 2)" |> f eqt
      code"println(if (readInt>0) 1 else 3)"
    
    code"Option(readInt).filter(_ > 0).fold(0)(_ + 1)" |> f eqt
      code"Option(readInt).filter(_ > 0).fold(0)(_ + 2)"
    
  }
  
  
}
