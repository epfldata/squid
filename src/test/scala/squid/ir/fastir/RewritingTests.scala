package squid
package ir
package fastir

class RewritingTests extends MyFunSuiteBase(RewritingTests.Embedding) {
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
  
  test("Substitution should be called from inside a reification context") {
    val a = ir"readDouble" rewrite {
      case ir"readDouble" => ir"42.toDouble"
    }
    assert(a =~= ir"42.toDouble")
  }
  
  test("Code generation should handle a hole in return position") {
    val a = ir"val a = 10.toDouble; val b = 22.toDouble; a + b" rewrite {
      case ir"val a = 10.toDouble; ($body:Double)" => ir"readDouble"
    }
    assert(a =~= ir"readDouble")
  }
  
  test("Rewriting sequences of bindings") {
    val a = ir"val a = readInt; val b = readDouble.toInt; a + b" rewrite {
      case ir"readDouble.toInt" => ir"readInt"
    }
    assert(a =~= ir"val a = readInt; val b = readInt; a + b")
  }
  
  test("Rewriting with HOPHoles") {
    val a = ir"val a = 11.toDouble; val b = 22.toDouble; val c = 33.toDouble; (a,b,c)" rewrite {
      case ir"val a = ($x:Int).toDouble; val b = ($y:Int).toDouble; ($body(a, b): Tuple3[Double, Double, Double])" =>
        ir"val a = ($x+$y).toDouble/2; $body(a, a)"
    }
    val f = ir"(x: Double, y: Double) => (x, y, 33.toDouble)"
    assert(a =~= ir"val a = (11+${ir"22"}).toDouble/2; $f(a, a)")
  }
  
  test("Rewriting lambdas") {
    val l = ir"(x: Double) => x * 2"
    
    val a = ir"val a = 11.toDouble; val f = $l; f(a)" rewrite {
      case ir"(x: Double) => x * 2" => ir"(x: Double) => x * 4"
    }
    val l0 = ir"(x: Double) => x * 4"
    assert(a =~= ir"val a = 11.toDouble; val f = $l0; f(a)")
  }
  
  test("Rewriting should happen at all occurences") {
    val a = ir"val a = Option(11).get; val b = 22; val c = Option(33).get; a + b + c" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(a =~= ir"val a = Option(11).get; val b = 22; val c = Option(33).get; ${ir"11"} + 22 + 33")
    
    val b = ir"val a = Option(Option(11).get).get; val b = 22; a + b" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(b =~= ir"val t1 = Option(11).get; val t2 = Option(11).get; ${ir"11"} + 22")
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
