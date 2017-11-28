package squid
package feature

class NestedQuoting extends MyFunSuite {
  
  import TestDSL.Predef._
  
  
  test("Simple Nesting") {
    
    assert(code"42.toString * 2" =~= code"42.toString * 2")
    
    assert(code"42.toString * 2" =~= code"${ code"42.toString" } * 2")
    
  }
  
  
  test("Block Nesting") {
    
    assert(code"42.toString * 2" =~= code"${ val n = code"42"; code"$n.toString" } * 2")
    
    assert(code"42.toDouble.toString * 2" =~= code"${ val n = code"42.toDouble"; code"$n.toString" } * 2")
    
  }
  
  
  test("Double Nesting") {
    
    assert(code"42.toDouble.toString * 2" =~= code"${ val str = code"${ val n = code"42"; code"$n.toDouble" }.toString"; str } * 2")
    
    assert(code"42.toDouble.toString * 2" =~= code"${ val n = code"42"; val str = code"${ code"$n.toDouble" }.toString"; str } * 2")
    
  }
  
  
  
  
}





