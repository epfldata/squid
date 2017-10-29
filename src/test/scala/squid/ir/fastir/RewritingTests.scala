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
    assert(b =~= ir"42f")

    val c = ir"42.toDouble" rewrite {
      case ir"(${Const(n)}: Int).toDouble" => ir"${Const(n.toDouble)}"
    }
    assert(c =~= ir"42.0")
  }

  test("Rewriting subpatterns") {
    val a = ir"(readInt + 111) * .5" rewrite {
      case ir"(($n: Int) + 111) * .5" => ir"$n * .25"
    }
    assert(a =~= ir"readInt * .25")

    val b = ir"(x: Int) => (x-5) * 32" rewrite {
      case ir"($b: Int) * 32" => ir"$b"
    }
    assert(b =~= ir"(x: Int) => x - 5")

    val c = ir"Option(42).get" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(c =~= ir"42")

    val d = ir"val a = Option(42).get; a * 5" rewrite {
      case ir"Option(($n: Int)).get" => n
      case ir"($a: Int) * 5" => ir"$a * 2"
    }
    assert(d =~= ir"val a = 42; a * 2")
  }

  test("Rewriting simple expressions only once") {
    val a = ir"println((50, 60))" rewrite {
      case ir"($x:Int,$y:Int)" => ir"($y:Int,$x:Int)"
      case ir"(${Const(n)}:Int)" => Const(n+1)
    } alsoApply println
    assert(a =~= ir"println((61,51))")
  }
}

object RewritingTests {
  object Embedding extends FastANF
}
