package squid
package feature

import utils._

class PrettyPrinting extends MyFunSuite {
  import TestDSL.Predef._
  import TestDSL.Quasicodes._
  import TestDSL.showRep
  
  test("Basic Types") {
    
    same(code"Option.empty"
      .rep |> showRep, "scala.Option.empty[scala.Nothing]")
    same(code"Option.empty[Int]"
      .rep |> showRep, "scala.Option.empty[scala.Int]")
    same(code"Option.empty[AnyRef]"
      .rep |> showRep, "scala.Option.empty[java.lang.Object]")
    
  }
  
  test("Null variables") {
    
    same(code"var x: Int = ${nullValue[Int]}; x+1"
      .rep |> showRep, """{
      |  var x_0: scala.Int = 0;
      |  x_0.+(1)
      |}""".stripMargin)
    same(code"var x: Int = null.asInstanceOf[Int]; x+1"
      .rep |> showRep, """{
      |  var x_0: scala.Int = null.asInstanceOf[scala.Int];
      |  x_0.+(1)
      |}""".stripMargin)
    same(code"var x: Int = ${code"null".asInstanceOf[Code[Int,Any]]}; x+1"
    // ^ Warning: variable `[x:squid.lib.package.Var[Int]]` of type `Int` (not a subtype of `AnyRef`) is assigned `null`.
      .rep |> showRep, """{
      |  var x_0: scala.Int = null;
      |  x_0.+(1)
      |}""".stripMargin)
    same(code"var x: String = ${nullValue[String]}; x+1"
      .rep |> showRep, """{
      |  var x_0: java.lang.String = null;
      |  x_0.+(1)
      |}""".stripMargin)
    same(code"var x: String = null; x+1"
      .rep |> showRep, """{
      |  var x_0: java.lang.String = null;
      |  x_0.+(1)
      |}""".stripMargin)
    
  }
  
  test("Free variables") {
    
    same(code"(?x:Int)+1".toString, """code"?x.+(1)"""")
    
  }
  
}
