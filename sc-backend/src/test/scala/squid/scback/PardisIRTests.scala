package squid.scback

import ch.epfl.data.sc.pardis
import ch.epfl.data.sc.pardis.ir.PardisApply
import squid.utils._

import collection.mutable.ArrayBuffer

class PardisIRTests extends PardisTestSuite {
  
  import Sqd.Predef._
  import Sqd.Quasicodes._
  import Sqd.{block}
  
  
  test("Folding of Simple Expressions") {
    
    val a = code"val x = 42; println(x); x"
    assert(stmts(a).size == 1)
    assert(ret(a) == base.const(42))
    
    val b = code"val x = 42; val y = x; val z = y; println(z); z"
    //println(b)
    assert(stmts(b) match {
      case s :: Nil =>
        //println(s.rhs,stmts(ir{println(42)}).head.rhs)
        s.rhs == stmts(ir{println(42)}).head.rhs
      case _ => fail
    })
    assert(ret(a) == base.const(42))
    
  }
  
  
  test("Code Insertion") {
    
    def f(a: Code[Int,{}], b: Code[Int,{}]) = ir{ $(a) + $(a) + $(b) }
    
    val q = ir{ $( f(ir{1.5.toInt}, ir{666}) ) + 1 }
    //println(q)
    
    assert(stmts(q).size == 4)
    
  }
  
  
  test("Code Insertion of Effects") {
    // Note: interestingly, in Squid ir".. outer .. ${ inner } .." executes the `inner` code in the middle of the
    // construction of `outer` tree... so the statements will be directly generated and aggregated in the enclosing block,
    // unlike what happens if `inner` is built outside the quote (also tested here).
    
    val a = code"val x = 42; println(x); x"
    //println(a)  // ir"{ val x2 = println(42); 42 }"
    assert(stmts(a).size == 1)
    
    val b0 = code" ${ code"val x = 42.toDouble; println(x); x" } + 1.0"
    //println(b0)  // ir"{ val x1 = 42.toDouble; val x3 = println(x1); val x5 = x1.+(1.0); x5 }"
    assert(stmts(b0).size == 3)
    
    val b1 = { val ins = code"val x = 42.toDouble; println(x); x"; code"$ins + 1.0" }
    //println(b1)  // ir"{ val x1 = 42.toDouble; val x3 = println(x1); val x5 = x1.+(1.0); x5 }"
    assert(stmts(b1).size == 3)
    
    val c0 = code"println(0); ${ code"println(1); println(2)" }; println(3); ()"
    //println(c0)  // ir"{ val x6 = println(0); val x7 = println(1); val x8 = println(2); val x9 = println(3); () }"
    assert(stmts(c0).size == 4)
    
    val c1 = { val ins = code"println(1); println(2)"; code"println(0); $ins; println(3); ()" }
    //println(c1)  // ir"{ val x6 = println(0); val x7 = println(1); val x8 = println(2); val x9 = println(3); () }"
    assert(stmts(c1).size == 4)
    
    val d0 = code"println(0); ${ code"println(1); println(2)" }"
    //println(d0)  // ir"{ val x12 = println(0); val x13 = println(1); val x14 = println(2); x14 }"
    assert(stmts(d0).size == 3)
    
    val d1 = { val ins = code"println(1); println(2)"; code"println(0); $ins" }
    //println(d1)  // ir"{ val x12 = println(0); val x13 = println(1); val x14 = println(2); x14 }"
    assert(stmts(d1).size == 3)
    
  }
  
  
  test("Blocks & Bindings") {
    
    val q = block(ir{ val n = 0; val a = new ArrayBuffer[Int](n); val b = 1; val c = a append 1; println(c) })
    //println(q)  // ir"{ val a2 = new ArrayBuffer[Int](0); val c5 = a2.append(1); val x7 = println(c5); x7 }"
    assert(stmts(q).size == 3)
    
  }
  
  
  //test("Blocks") {}  // TODO
  
  
  test("Scheduling Subexpressions") {
    
    sameDefs(ir{ println(1.toDouble);println(2.toDouble) },
             ir{ val n1 = 1.toDouble; val p1 = println(n1); val n2 = 2.toDouble; val p2 = println(n2); p2 })
    
    sameDefs(ir{ val arr = new ArrayBuffer[Int](); arr append 1; val o = Option(arr.size) },
             ir{ val arr = new ArrayBuffer[Int](); val a = arr append 1; val s = arr.size; val o = Option(s); () })
    
    sameDefs(ir{ val arr = new ArrayBuffer[Int](); arr append 1; arr.size+1 },
             ir{ val arr = new ArrayBuffer[Int](); val a = arr append 1; val s = arr.size; s+1 })
    
    sameDefs(ir{ (1.toDouble+1.0,2.toDouble+2.0) },
             ir{ val n1 = 1.toDouble; val n11 = n1+1.0; val n2 = 2.toDouble; val n22 = n2+2.0; Tuple2(n11,n22) })
    
    sameDefs(ir{ 1.toDouble+2.toDouble+3.toDouble },
             ir{ val n1 = 1.toDouble; val n2 = 2.toDouble; val p1 = n1 + n2; val n3 = 3.toDouble; val p2 = p1 + n3; p2 })
    
  }
  
  
  test("By-Name Parameters") {
    
    val t0 = code"Option(42) getOrElse {println(0); 666}"
    assert(stmts(t0).size == 2)
    assert(stmts(t0)(1).rhs.funArgs(1).asInstanceOf[pardis.ir.PardisBlock[_]].stmts.size == 1)
    
    val t1 = code"Option(()) getOrElse {val r = println(0); r}"
    assert(stmts(t1).size == 2)
    
    val t2 = code""" Option[String](null) getOrElse "42" """
    assert(stmts(t2).size == 2)
    
    //println(ir"None") // There is no auto-binding for this (in fact, not even a mirror defined for it in SC's ScalaCore)
    //println(ir"None getOrElse 42") // Note: this will pass the block for `42` as the first argument to the generic Option's getOrElse, and result in a cast crash...
    
    // Note: also test Option.empty when it is in SC
    
  }
  
  
  test("Types") {
    
    val ABI = SC.typeArrayBuffer(SC.typeInt)
    
    assert(ir{ new ArrayBuffer[Int] }.typ.rep == ABI)
    
    assert(ir{ val n1 = 1.toDouble.toInt; ArrayBuffer(n1) }.typ.rep == ABI)
    
    assert(stmts(ir{ val n1 = 1.toDouble }).head.typeT == typeRepOf[Double])
    
  }
  
  
  test("Manual Inlining") {
    
    val f = code"(x: Int) => x+1"
    val p = code"$f(42)"
    
    assert(stmts(p).size == 2)
    assert(stmts(p)(1).rhs.isInstanceOf[PardisApply[_,_]])
    
    val p2 = Sqd.inline(f,code"42")
    
    sameDefs(p2, code"val a = 42; a + 1")
    
  }
  
  
  test("Function3") {
    
    sameDefs(code"(a:Int,b:Int,c:Double) => a * b + c", {
      import SC._
      import SC.Predef.typeLambda3
      scBlock{ __lambda((a:Rep[Int],b:Rep[Int],c:Rep[Double]) => a * b + c) }
    })
    
    sameDefs(code"((a:Int,b:Int,c:Double) => a * b + c)(1,2,3)", {
      import SC._
      import SC.Predef.typeLambda3
      scBlock{ __app(__lambda((a:Rep[Int],b:Rep[Int],c:Rep[Double]) => a * b + c)) apply (unit(1), unit(2), unit(3.0)) }
    })
    
  }
  
  
  test("Variables") {
    import squid.lib.Var
    import SC._
    
    sameDefs(code"var a = 0; 1", scBlock {
      val a = __newVar(unit(0))
      unit(1)
    })
    sameDefs(code"var a = 0; a + 1", scBlock {
      val a = __newVar(unit(0))
      __readVar(a) + unit(1)
    })
    sameDefs(code"var a = 0; a = a + 1; a", scBlock {
      val a = __newVar(unit(0))
      __assign(a,__readVar(a) + unit(1))
      __readVar(a)
    })
    
  }
  
  
  test("Variable dependency and order") {
    import squid.lib.Var
    import SC.Predef._
    import SC.{ ArrayBufferRep, readVar }
    
    sameDefs(code"val ab = new ArrayBuffer[Int]; ab.append(1); var s = ab.size; s", scBlock {
      val ab = SC.__newArrayBuffer[Int]()
      ab.append(unit(1))
      val s = SC.__newVar(ab.size)
      s
    })
    
  }
  
  
  test("Inserting Variables") {
    import squid.lib.Var
    
    sameDefs(code"var a = 0; a; a = a + 1; a", block {
      val v = code"Var(0)"
      code"$v := $v.! + 1; $v.!"
    })
    
    sameDefs(code"var a = 0; a = a + 1; a", {
      val v = code"Var(0)"
      code"$v := $v.! + 1; $v.!"
    })
    
    sameDefs(code"var a = 0; a = a + 1; a", block {
      import SC.typeInt
      val v = SC.__newVar(SC.unit(0))
      code"$v := $v.! + 1; $v.!"
    })
    
    sameDefs(code"var a = 0; a = a + 1; a", block {
      val v = mkVar(code"0")
      code"$v := $v.! + 1; $v.!"
    })
    
  }
  
  
  test("Special Pardis Operations") {
    
    import SC.{ AllRepOps, DoubleRep, infix_hashCode, infix_toString, infix_asInstanceOf, arrayBufferNew2, arrayBufferApplyObject, typeArrayBuffer }
    import SC.Predef._
    
    sameDefs(ir{ 42 == 42.0.toInt },
      scBlock { unit(42) __== unit(42.0).toInt })
    
    sameDefs(ir{ 42## },
      scBlock { infix_hashCode(unit(42)) })
    
    sameDefs(ir{ "ok"## },
      scBlock { infix_hashCode(unit("ok")) })
    
    sameDefs(ir{ true.toString },
      scBlock { infix_toString(unit(true)) })
    
    sameDefs(ir{ ArrayBuffer().toString },
      scBlock { infix_toString(arrayBufferApplyObject[Nothing]())(typeArrayBuffer[Nothing](typeNothing)) })
    
    sameDefs(ir{ (new ArrayBuffer).asInstanceOf[ArrayBuffer[Int]] },
      scBlock { infix_asInstanceOf[ArrayBuffer[Int]](arrayBufferNew2[Nothing]) })
    
  }
  
  
  test("Scala Boolean By-Name Inconsistecies") {
    
    val r = block {
      
      val bg = code"new ArrayBuffer[String]"
      val ol_number = mkVar(code"32")
      
      code"""
        if ("ok".length > 0 || 42.toDouble > 0.0 && 0.toDouble < 42.0)
          $bg($ol_number!) = "B"
        else
          $bg($ol_number!) = "G"
      """
    }
    
    import SC.{ AllRepOps, DoubleRep, typeArrayBuffer, StringRep, IntRep, BooleanRep }
    import SC.Predef._
    
    sameDefs(r, scBlock {
      val a = SC.arrayBufferNew2[String]
      val v = SC.__newVar(unit(32))
      SC.__ifThenElse(
        { unit("ok").length > unit(0) || unit(42).toDouble > unit(0.0) && unit(0).toDouble < unit(42.0) },
        { SC.arrayBufferUpdate(a,SC.__readVar(v),unit("B")) },
        { SC.arrayBufferUpdate(a,SC.__readVar(v),unit("G")) }
      )
    })
    
  }
  
  
  test("SC.Rep[T] Conversion Helper") {
    
    assert(stmts(block{
      code"42.toDouble".toRep : SC.Rep[Double]
    }).head.rhs.isInstanceOf[SC.IntToDouble])
    
    assertDoesNotCompile("""
      code"42.toDouble".toRep : SC.Rep[Int]
    """)
    
  }

  test("Hole Substitution"){
    def power[C](n: Int, x: Code[Double,C]): Code[Double,C] =
      if (n > 0) code"${power(n-1, x)} * $x"
      else code"1.0"

    sameDefs(ir{
      val x = 5.0
      val x_3 = ${power(3, code"$$x : Double")}
    }, code"val x = 5.0; val x_3 = 1.0 * x * x * x")
  }
  
  test("SC.Rep[T] Function Helper") {
    import SC.Predef._
    
    sameDefs(ir{
      val n = ArrayBuffer(1)(0)
      val r = $(mapLambda(code"$$n:Int")(x => SC.IntRep(x)+SC.unit(42)))
      r/2
    }, ir{
      val m = ArrayBuffer(1)(0)
      (m+42)/2
    })
    
  }
  
  
}
