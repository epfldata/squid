package squid
package ir
package fastir

import utils._

class HigherOrderPatternVariables extends MyFunSuite {
  import TestDSL.Predef._

  test("Matching lambda bodies") {

    val id = ir"(z:Int) => z"

    ir"(a: Int) => a + 1" matches {
      case ir"(x: Int) => $body(x):Int" =>
        body eqt ir"(_:Int)+1"
    } and {
      case ir"(x: Int) => $body(x):$t" =>
        body eqt ir"(_:Int)+1"
        eqt(t, irTypeOf[Int])
    } and {
      case ir"(x: Int) => ($exp(x):Int)+1" =>
        exp eqt id
    }

    ir"(a: Int, b: Int) => a + 1" matches {
      case ir"(x: Int, y: Int) => $body(y):Int" => fail
      case ir"(x: Int, y: Int) => $body(x):Int" =>
    } and {
      case ir"(x: Int, y: Int) => $body(x,y):Int" =>
    }

    ir"(a: Int, b: Int) => a + b" matches {
      case ir"(x: Int, y: Int) => $body(x):Int" => fail
      case ir"(x: Int, y: Int) => $body(x,y):Int" =>
        body eqt ir"(_:Int)+(_:Int)"
    } and {
      case ir"(x: Int, y: Int) => ($lhs(y):Int)+($rhs(y):Int)" => fail
      case ir"(x: Int, y: Int) => ($lhs(x):Int)+($rhs(y):Int)" =>
        lhs eqt id
        rhs eqt id
    }

  }

  test("Matching let-binding bodies") {

    ir"val a = 0; val b = 1; a + b" matches {
      case ir"val x: Int = $v; $body(x):Int" =>
        v eqt ir"0"
        body matches {
          case ir"(y:Int) => { val x: Int = $w; $body(x,y):Int }" =>
            w eqt ir"1"
            body eqt ir"(u:Int,v:Int) => (v:Int)+(u:Int)"
        }
    }
  }

  test("Find a good name") {
    val a = ir"val a = 10.toDouble; val b = a + 1; b" rewrite {
      case ir"val x = 10.toDouble; $body(x):Double" => body(ir"readDouble")
    }
    assert(a == ir"val r = readDouble + 1; r")

    // val b = ir"val a = 10; val b = readInt; val c = a + b; c" rewrite {
    //   case ir"val x = 10; val y = readInt; $body(x): Int" => ir"$body(42)"
    //   // case ir"val x = 10.toDouble; $body(x):Double" => body(ir"readDouble")
    // } alsoApply println
    // assert(b == ir"readDouble.toInt + 42")
    // assert(b == ir"val r = readDouble + 1; r")
  }

}
