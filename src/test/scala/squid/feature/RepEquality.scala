package squid
package feature

class RepEquality extends MyFunSuite {
  
  import TestDSL.Predef._
  
  test("Functions") {
    
    assert(code"(x: Int) => x" =~= code"(x: Int) => x")
    
    assert(code"(x: Int) => x" =~= code"(y: Int) => y")
    
    assert(code"val x = 42.toDouble; x + 1" =~= code"val y = 42.toDouble; y + 1")
    
  }
  
  
  
}
