package squid
package feature

import utils._

class Subs extends MyFunSuite {
  import TestDSL.Predef._
  
  val a2b = code"($$a: Int) * 2 + ($$b: Int)"
  
  test("subs Basics") {
    
    eqt(code"$$a: Int" subs 'a -> code"42",  code"42")
    
    eqt(a2b subs 'b -> code"$$a: Int",  code"($$a: Int) * 2 + ($$a: Int)")
    eqt(a2b subs 'b -> code"$$a: Int" subs 'a -> code"42",  code"(42: Int) * 2 + (42: Int)")
    
    val f = code"(x: Int) => x + 1"
    f match {
      case code"(y: Int) => $body" =>
        val r = code"(z: Int) => ${ body subs 'y -> code"$$z: Int" }"
        eqt(r, f)
    }
    
    assertDoesNotCompile(""" a2b subs ('a, code"42") """) // Error:(26, 9) Illegal syntax for `subs`; Expected: `term0.subs 'name -> term1`
    assertDoesNotCompile(""" code"42" subs 'a -> code"42" """) // Error:(9, 10) This term does not have a free variable named 'a' to substitute.
    assertDoesNotCompile(""" a2b subs 'b -> code"4.2" """) // Error:(27, 20) Cannot substitute free variable `b: Int` with term of type `Double`
    
  }
  
  test("subs Context") {
    
    (a2b subs 'a -> code"42" : Code[Int, {val b: Int}])
    
    assertDoesNotCompile(""" (a2b subs 'a -> code"42" : Code[Int,{}]) """) // Error:(34, 11) type mismatch; found: scp.TestDSL2.Predef.base.IR[Int,Any with Any{val b: Int}]; required: scp.TestDSL2.Predef.IR[Int,AnyRef]
    assertDoesNotCompile(""" (a2b subs 'a -> code"42" run) """) // Error:(35, 29) Cannot prove that AnyRef <:< Any with Any{val b: Int}.
    assertDoesNotCompile(""" (code"($$a: Int)+1" subs 'a -> code"$$a: Int" run) """) // Error:(39, 47) Cannot prove that AnyRef <:< Any{val a: Int} with Any.
    
    assert( (a2b subs 'a -> code"42" subs 'b -> code"666" run) == 42 * 2 + 666 )
    a2b subs 'a -> code"$$a: Int" : Int Code {val a: Int; val b: Int}
    a2b subs 'a -> code"$$a: Int" withContextOf a2b
    
    val t0 = a2b subs 'a -> code"$$x: Int"
    t0 ofType[ Int Code Any{val x: Int; val b: Int} ]() // Note: Any{...} is more general than {...}, so we need Any here
    
    val t1 = a2b subs 'a -> code"($$b: Double) toInt"
    t1 ofType[ Int Code Any{val b: Int with Double} ]()
    
  }
  
  test("subs Abstracted Context") {
    
    def foo[C](x: Double Code C) = {
      val q = code"$x.toInt + ($$z: Symbol).toString.length" : Int Code C{val z:Symbol}
      var r: Int Code C{val a: Int; val z: Symbol} = null
      r = a2b subs 'b -> q
      r
    }
    
    var x: Double Code Any{val b: Boolean} = null
    x = code"if ($$b: Boolean) 0.0 else 1.0"
    var f: Int Code {val b: Boolean; val a: Int; val z: Symbol} = null
    f = foo(x)
    
    val r = f subs 'b -> code"true" subs 'a -> code"42" subs 'z -> code" 'ok "
    eqt(r: Int Code {}, code" (42:Int) * 2 + ((if (true) 0.0 else 1.0).toInt + 'ok.toString.length) ")
    same(r.run, 42 * 2 + 3)
    
  }
  
  test("subs with Complex Replacement") {
    
    // FIXME: properly untypecheck patmat in macro or find another solution
    //a2b dbg_subs 'a -> { ir"42" match { case ir"42" => ir"42" } }
    
  }
  
}
