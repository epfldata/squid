package squid
package ir
package fastir

class HigherOrderPatternVariables extends MyFunSuiteBase(HigherOrderPatternVariables.Embedding) {
  import HigherOrderPatternVariables.Embedding.Predef._

  test("Matching lambda bodies") {

    val id = ir"(z:Int) => z"

    ir"(a: Int) => a + 1" matches {
      case ir"(x: Int) => $body(x): Int" => assert(body == ir"(_:Int) + 1")
      case ir"(x: Int) => $body(x):$t" => assert(body == ir"(_:Int)+1")
      case ir"(x: Int) => ($exp(x):Int)+1" => assert(exp == id)
    }

    ir"(a: Int, b: Int) => a + 1" matches {
      case ir"(x: Int, y: Int) => $body(y):Int" => fail
      case ir"(x: Int, y: Int) => $body(x):Int" =>
    } and {
      case ir"(x: Int, y: Int) => $body(x,y):Int" =>
    }

    ir"(a: Int, b: Int) => a + b" matches {
      case ir"(x: Int, y: Int) => $body(x):Int" => fail
      case ir"(x: Int, y: Int) => $body(x,y):Int" => assert(body == ir"(_:Int)+(_:Int)")
    }

    ir"(a: Int, b: Int) => a + b" matches {
      case ir"(x: Int, y: Int) => ($lhs(y):Int)+($rhs(y):Int)" => fail
      case ir"(x: Int, y: Int) => ($lhs(x):Int)+($rhs(y):Int)" =>
        assert(lhs == id)
        assert(rhs == id)
    }
  }

  test("Matching let-binding bodies") {
    // Not implemented error in `letin`
    //ir"val a = 0; val b = 1; a + b" matches {
    //  case ir"val x: Int = $v; $body(x):Int" =>
    //    assert(v == ir"0")
    //    body matches {
    //      case ir"(y:Int) => { val x: Int = $w; $body(x,y):Int }" =>
    //        assert(w == ir"1")
    //        assert(body == ir"(u:Int,v:Int) => (v:Int)+(u:Int)")
    //    }
    //}
  }

  test("Non-trivial arguments") {
    val id = ir"(z: Int) => z"

    ir"(a: Int, b: Int) => a + b" matches {
      case ir"(x: Int, y: Int) => $body(x + y): Int" => assert(body == id)
      case ir"(x: Int, y: Int) => $body(x): Int" => fail
      case ir"(x: Int, y: Int) => $body(y): Int" => fail
    }

    ir"(a: Int, b: Int, c: Int) => a + b + c" matches {
      case ir"(x: Int, y: Int, z: Int) => $body(x + y, z): Int" => assert(body == ir"(r: Int, s: Int) => r + s")
    }

    ir"(a: Int, b: Int, c: Int) => a + b + c" matches {
      case ir"(x: Int, y: Int, z: Int) => $body(x + y + z): Int" => assert(body == id)
    }

    // TODO `extract` should see the different combinations of `x + y + z`
    // case ir"(x: Int, y: Int, z: Int) => $body(x + z, y)" => println(body); assert(body == ir"(r: Int, s: Int) => r + s")

    // TODO doesn't "align", `extract` is too structural
    // case ir"(x: Int, y: Int, z: Int) => $body(x, y + z)" => assert(body == ir"(r: Int, s: Int) => r + s")

    ir"(a: Int) => readInt + a" matches {
      case ir"(x: Int) => $body(readInt, x): Int" => assert(body == ir"(r: Int, s: Int) => r + s")
    }

    ir"(a: Int) => readInt + a" matches {
      case ir"(x: Int) => $body(x, readInt): Int" => assert(body == ir"(r: Int, s: Int) => s + r")
    }

    ir"(a: Int, b: Int) => readInt + (a + b)" matches {
      case ir"(x: Int, y: Int) => $body(readInt, x + y): Int" => assert(body == ir"(r: Int, s: Int) => r + s")
    }

    // TODO doesn't "align", `extract` is too structural
    //ir"(a: Int, b: Int) => readInt + (a + b)" matches {
    //  case ir"(x: Int, y: Int) => $body(x + y, readInt): Int" => assert(body == ir"(r: Int, s: Int) => s + r")
    //}
  }

  //test("Currying") {
  //  ir"(a: Int, b: Int) => a + b" match {
  //    case ir"(x: Int, y: Int) => $body(x)(y)" =>
  //  }
  //}

  test("Match letbindinds") {
    // TODO `apply` should call inline
    //val a = ir"val a = 10.toDouble; val b = a + 1; val c = b + 2; c" matches {
    //  case ir"val x = 10.toDouble; $body(x):Double" =>
    //    assert(ir"$body(42)" == ir"(val a = (x: Int) => (val b = x + 1; val c = b + 2; c)); val tmp = a.apply(42.0); tmp")
    //}

    // val b = ir"val a = 10; val b = readInt; val c = a + b; c" rewrite {
    //   case ir"val x = 10; val y = readInt; $body(x): Int" => ir"$body(42)"
    //   // case ir"val x = 10.toDouble; $body(x):Double" => body(ir"readDouble")
    // } alsoApply println
    // assert(b == ir"readDouble.toInt + 42")
    // assert(b == ir"val r = readDouble + 1; r")
  }
}

object HigherOrderPatternVariables {
  object Embedding extends FastANF
}
