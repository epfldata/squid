package squid
package ir
package fastir

class RewritingTests extends MyFunSuiteBase(BasicTests.Embedding) {
  import RewritingTests.Embedding.Predef._

  test("Simple rewrites") {
    val a = ir"123" rewrite {
      case ir"123" => ir"666"
    }
    assert(a =~= ir"666")

    val b = ir"42.toFloat" rewrite {
      case ir"42.toFloat" => ir"42f"
    }
    assert(b =~= ir"val t = ${ir"42"}.toFloat; 42f")

    val c = ir"42.toDouble" rewrite {
      case ir"(${Const(n)}: Int).toDouble" => ir"${Const(n.toDouble)}"
    }
    assert(c =~= ir"val t = ${ir"42"}.toDouble; 42.0")

    //assertDoesNotCompile("""
    //  T.rewrite { case ir"0.5" => ir"42" }
    //""")

    //assertDoesNotCompile("""
    //  T.rewrite { case ir"123" => ir"($$n:Int)" }
    //""")
  }

  test("Rewriting subpatterns") {
    val a = ir"(10.toDouble + 111) * .5" match {
      case ir"(($n: Double) + 111) * .5" => ir"$n * .25"
    }
    assert(a =~= ir"10.toDouble * .25")

    val b = ir"Option(42).get" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(b =~= ir"val t = Option(42).get; 42")

    val c = ir"val a = Option(42).get; a * 5" rewrite {
      case ir"Option(($n: Int)).get" => n
      case ir"($a: Int) * 5" => ir"$a * 2"
    }
    assert(c =~= ir"val t1 = Option(42); val t2 = t1.get; val t3 = ${ir"42"} * 5; ${ir"42"} * 2")
  }
  
  test("Rewriting with dead-ends") {
    val b = ir"Option(42).get; 20" rewrite {
      case ir"Option(($n: Int)).get; 20" => n
    }
    assert(b =~= ir"val t = ${ir"Option(42)"}; 42")
  } 
  
  //test("Rewriting with impures") {
  //  val a = ir"val a = readInt; val b = readInt; (a + b) * 0.5" rewrite {
  //    case ir"(($h1: Int) + ($h2: Int)) * 0.5" => dbg_ir"($h1 * $h2) + 42.0"
  //  }
  //  assert(a =~= ir"(readInt + readInt) + 42.0")
  //}

  //test("Rewriting simple expressions only once") {
  //  val a = ir"println((50, 60))" rewrite {
  //    case ir"($x:Int,$y:Int)" => ir"($y:Int,$x:Int)"
  //    //case ir"(${Const(n)}:Int)" => Const(n+1)
  //  }
  //  assert(a =~= ir"println((61,51))")
  //}
  //
  //test("Function Rewritings") {
  //  val a = ir"(x: Int) => (x-5) * 32" rewrite {
  //    case ir"($b: Int) * 32" => ir"$b"
  //  }
  //  assert(a =~= ir"(x: Int) => x - 5")
  //
  //  val b = ir"(x: Int) => (x-5) * 32" rewrite {
  //    case ir"(x: Int) => ($b: Int) * 32" => dbg_ir"val x = 42; (p: Int) => $b + p"
  //  } alsoApply println
  //
  //  println(ir"val u = 42; (v: Int) => (u - 5) + v")
  //
  //  assert(b =~= ir"val u = 42; (v: Int) => (u - 5) + v")
  //}
}

object RewritingTests {
  object Embedding extends FastANF
}
