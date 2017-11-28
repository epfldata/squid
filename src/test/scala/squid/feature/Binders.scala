package squid
package feature

class Binders extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Val Defs") {
    // TODO test type-ascribed val; test scope extrusion check
    
    val ap1 = code"val a = 0; a+1"
    
    assertDoesNotCompile(""" ap1 match { case code"val x = $init; $body" => } """) // Error:(13, 22) Embedding Error: No type info for hole 'init', in: { ...
    
    val b = ap1 match {
      case code"val x = $init: Int; $body" =>
        eqt(init: Q[Int,{}], code"0")
        assert(init.trep <:< typeRepOf[Int])
        eqt(body: Q[Int,{val x: Int}], code"($$x:Int)+1")
        eqt(body.trep, typeRepOf[Int])
        body
    }
    
    /*
    // interestingly, this compiles but assumes type Any for 'body' (which should be safe)
    // ^ no more: removed ascription of the matched term when it was ascribing Any
    ap1.erase match {
      case ir"val x = $init: Int; $body" =>
        eqt(body: Q[Any,{val x: Int}], ir"($$x:Int)+1")
        eqt(implicitTypeOf(body), typeRepOf[Any])
    }
    */
    
    val b2 = code"$b * 2"
    eqt(b2, code"(($$x:Int)+1)*2")
    
    assertDoesNotCompile(""" b2.run """) // Error:(26, 8) Cannot prove that AnyRef <:< Any{val x: Int}.
    
    same(code"val x = 42; $b2".run, 86)
    
  }
  
  test("Nested Val Defs") {
    
    code"val a = String.valueOf(123456789); val b = 3; a take b" matches {
      case code"val a: $at = $a; val b: $bt = $b; $body: $bodyt" =>
        eqt(at.rep, typeRepOf[String])
        assert(bt <:< codeTypeOf[Int])
        eqt(bodyt.rep, typeRepOf[String])
        eqt(a, code"String.valueOf(123456789)")
        eqt(b, code"3")
        eqt(body, code"($$a:String) take $$b")
    } and {
      case code"val a: $at = $a; val b: Int = $b; $body: $bodyt" =>
        eqt(body, code"($$a:String) take $$b")
    }
    
    
  }
  
  test("Lambdas") {
    
    val lam = code"(arg: Int) => arg * 2"
    
    eqt(lam, code"(x: Int) => x * 2")
    
    lam match { case code"(_ * 2)" => }
    lam match { case code"(_ * (${Const(2)}: Int))" => }
    lam match { case code"(x => x * 2)" => }
    lam match { case code"(x => x * ($n: Int))" => eqt(n: Q[Int, {val x: Int}], code"2") }
    lam match { case code"((x: Int) => x * 2)" => }
    lam match { case code"(x => $body)" => eqt(body, code"($$x:Int)*2") }
    val b = lam match { case code"(x => $body: Int)" => eqt(body: Q[Int, {val x: Int}], code"($$x:Int)*2"); body }
    
    val b2 = code"$b * 2"
    
    assertDoesNotCompile(""" b2.run """)
    
  }
  
  test("Nested Lambdas") {
    
    val lamlam = code"(str: String) => (n: Int) => str take n"
    
    lamlam match {
      case code"(a: String) => (b: Int) => a take b" =>
    }
    val b = lamlam match {
      case code"(a => b => $body: String)" =>
        body match {
          case code"($a:String) take $b" =>
        }
        body: Q[String, {val a: String; val b: Int}]
    }
    
    assertDoesNotCompile(""" b2.run """)
    assertDoesNotCompile(""" code"val a = String.valueOf(123456789); $b".run """)
    
    same(code"val a = String.valueOf(123456789); val b = 3; $b".run, "123")
    
  }
  
  
}
