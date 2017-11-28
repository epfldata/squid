package squid
package functional

class Soundness extends MyFunSuite {
  import TestDSL.Predef._
  import Soundness._
  
  test("Term's Type Matching") {
    
    code"Some(42)".erase match {
        
      case code"Some[Nothing]($x:Nothing)" =>
        code"$x:String".run // would crash
        fail
        
      case code"Some[Any]($x)" =>
        // ok
        
    }
    
  }
  
  test("Function Matching") {
    val f = code"(x: Int) => x"
    f.erase match {
        
      case code"$f: (Any => Int)" =>
        code"$f(1.5)".run // would crash
        fail
        
      case code"$f: (Int => Any)" =>
        same(code"$f(15)".run, 15)
        
    }
  }
  
  test("Mutable References") {
    
    val r42 = code"Ref(42)".erase
    
    /* We used to check method call return types, now we don't (for flesibility reasons)
     * We also match method tparams covariantly.
     * This combination seems to lead to unsoundness... (see below) */
    r42 matches {
      
      case r @ code"Ref($v: Any)" => // Note: used to raise: // Warning:(33, 18) /!\ Type Any was inferred in quasiquote pattern /!\
      
    } and {
      
      case r @ code"Ref[Any]($_)" =>
        //ir"$r.value = 0.5" // does not compile: Error:(36, 9) Embedding Error: value value is not a member of Any
        // ^ would crash, but 'r' does not get the precise type inferred in the xtor -- it gets Quoted[Any,{}]
      
      // Note: with the 'x as y' pattern-synonym extractor, we could write 'case ir"$r as Ref[Any]($_)"'
      // but it should not match either (thanks to the return-type check in methodApp extraction)
      // EDIT -- now it would!
      
    }
    
    r42 match {
      //case r @ ir"Ref[Any]($_)" =>
      //  fail
        
      case code"$r: Ref[Any]" =>
        val unsound = code"$r.value = 0.5"
        unsound.run // would crash
        fail
      case code"$r: Ref[$t]" =>
        assertDoesNotCompile(""" dsl"$r.value = 0.5" """) // Error:(30, 9) Embedding Error: type mismatch; found: Double(0.5); required: t
        
    }
    
  }
  
  
}
object Soundness {
  case class Ref[A](var value: A)
}
