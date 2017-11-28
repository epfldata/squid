package squid
package functional

class FunBodyXion extends MyFunSuite {
  
  import TestDSL.Predef._
  
  val fun = code"(x: Int) => x + 1"
  val body = fun match {
    case code"(y: Int) => $b: Int" => b
  }
  
  test("Function Body Extraction") {
    
    //println(body, ir"($$y: Int) + 1")
    //println(body.rep extract ir"($$y: Int) + 1".rep)
    //println(ir"($$y: Int) + 1".rep extract body.rep)
    
    assert(body =~= code"($$y: Int) + 1")
    assert(!(body =~= code"($$x: Int) + 1"))
    
    val bodyPart = body match {
      case code"($x: Int) + 1" => x
    }
    assert(bodyPart =~= code"$$y: Int")
    assert(!(bodyPart =~= code"$$x: Int"))
    
  }
  
  test("Function Body Reconstruction") {
    
    val fun2 = code"(y: Int) => $body" : Q[Int => Int, {}]
    assert(fun =~= fun2)
    
  }
  
  
  
  
}



