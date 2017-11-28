package squid
package feature

import squid.ir.RewriteAbort
import utils._

class TrickyTypes extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Local Type Synonym") {
    
    code"Option.empty[String]" eqt {
      type String = java.lang.String
      code"Option.empty[String]"
    }
    
  }
  
  test("Local Type With Evidence") {
    
    class Lol
    
    assertDoesNotCompile("""
      code"Option.empty[Lol]"
    """)
    
    code"Option.empty[Int]" eqt {
      implicit val LolImpl = codeTypeOf[Int].asInstanceOf[CodeType[Lol]]
      code"Option.empty[Lol]"
    }
    
  }
  
  
  test("Explicit Empty Contexts and Inferred Contexts") {
    
    List[Code[Int,{}]](code"1", code"2", code"3").foldLeft(code"0") { (acc, exp) =>
      code"if ($acc != 0) $acc else $exp"
    }
    
  }
  
  
  test("Lambda with Expected Type") {
    import base.Quasicodes._
    
    val c1: Code[Int => Int => Bool => Bool,_] = ir{ (s:Int) =>
      val n = 42
      k => { b => b }
    }
    
    eqt(c1.typ, codeTypeOf[Int => Int => Bool => Bool])
    
  }
  
  
  def foo[T](x:Code[T,{}]) = code"$x==0"
  
  test("Any method called on type parameter") {
    foo(code"42") eqt code"${code"42:Any"} == 0"
    foo(code"42") neqt code"${code"42"} == 0" // Note: Int.== and Any.== have two different method symbols!!
  }
  
  
}
