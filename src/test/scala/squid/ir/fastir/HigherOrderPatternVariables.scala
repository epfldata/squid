package squid
package ir
package fastir

import scala.util.Try

class HigherOrderPatternVariables extends MyFunSuiteBase(HigherOrderPatternVariables.Embedding) {
  import HigherOrderPatternVariables.Embedding.Predef._

  test("Matching lambda bodies") {
    val id = ir"(z:Int) => z"

    ir"(a: Int) => a + 1" match {
      case ir"(x: Int) => $body(x): Int" => assert(body =~= ir"(_:Int) + 1")
    }

    ir"(a: Int) => a + 1" match {
      case ir"(x: Int) => $body(x):$t" => assert(body =~= ir"(_:Int)+1")
    }

    ir"(a: Int) => a + 1" match {
      case ir"(x: Int) => ($exp(x):Int)+1" => assert(exp =~= id)
    }

    assert(Try {
      ir"(a: Int, b: Int) => a + 1" match  {
        case ir"(x: Int, y: Int) => $body(y):Int" => fail
      }
    }.isFailure)

    ir"(a: Int, b: Int) => a + 1" match {
      case ir"(x: Int, y: Int) => $body(x):Int" =>
    }

    ir"(a: Int, b: Int) => a + 1" match {
      case ir"(x: Int, y: Int) => $body(x,y):Int" =>
    }


    ir"(a: Int, b: Int) => a + b" match {
      case ir"(x: Int, y: Int) => $body(x,y):Int" => assert(body =~= ir"(_:Int)+(_:Int)")
    }

    assert(Try {
      ir"(a: Int, b: Int) => a + b" match {
        case ir"(x: Int, y: Int) => $body(x):Int" => fail
      }
    }.isFailure)

    ir"(a: Int, b: Int) => a + b" match {
      case ir"(x: Int, y: Int) => ($lhs(x):Int)+($rhs(y):Int)" =>
        assert(lhs =~= id)
        assert(rhs =~= id)
    }

    assert(Try {
      ir"(a: Int, b: Int) => a + b" match {
        case ir"(x: Int, y: Int) => ($lhs(y):Int)+($rhs(y):Int)" =>
      }
    }.isFailure)
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
    
    ir"(a: Int, b: Int, c: Int) => a + b + c" matches {
      case ir"(x: Int, y: Int, z: Int) => $body(x + y, z): Int" => assert(body == ir"(r: Int, s: Int) => r + s")
    }

    ir"(a: Int, b: Int, c: Int) => a + b + c" match {
      case ir"(x: Int, y: Int, z: Int) => $body(x + y + z): Int" => assert(body =~= id)
    }

    ir"(a: Int) => readInt + a" match {
      case ir"(x: Int) => $body(readInt, x): Int" => assert(body =~= ir"(r: Int, s: Int) => r + s")
    }

    ir"(a: Int) => readInt + a" match {
      case ir"(x: Int) => $body(x, readInt): Int" => assert(body =~= ir"(r: Int, s: Int) => s + r")
    }

    ir"(a: Int, b: Int) => readInt + (a + b)" match {
      case ir"(x: Int, y: Int) => $body(readInt, x + y): Int" => assert(body =~= ir"(r: Int, s: Int) => r + s")
    }
  }

  test("Match letbindings") {
    ir"val a = 10.toDouble; a + 1" match {
      case ir"val x = 10.toDouble; $body(x)" => assert(body =~= ir"(_: Double) + 1")
    }

    ir"val a = 11.toDouble; val b = 22.toDouble; val c = 33.toDouble; (a,b,c)" match {
      case ir"val a = ($x:Int).toDouble; val b = ($y:Int).toDouble; $body(a, b)" =>
        assert(x =~= ir"11")
        assert(y =~= ir"22")
        assert(body =~= ir"(a: Double, b: Double) => (a, b, 33.toDouble)")
    }
    
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
  
  test("HOPHoles should be able to extract an impure statement") {
    val f = ir"(x: Int) => println(x + 1)"
    ir"val a = 20; $f(a)" match {
      case ir"(x: Int) => ($prt(x + 1): Int)" => assert(prt =~= ir"(x: Int) => println(x)")
    }
  }
  
  test("HOPHoles should extract all the occurences of the pattern") {
    ir"val f = (x: Int, y: Int) => { println(x + y); x + y }; f(11, 22)" match {
      case ir"(x: Int, y: Int) => ($h(x + y): Int)" => assert(h =~= ir"(x: Int) => { println(x); x }")
    }
  }
  
  test("HOPHoles should be able to extract nested letbindings") {
    ir"val a = readInt; val b = readInt; val a1 = a + 1; val b1 = b + 1; a1 + b1" match {
      case ir"($h(readInt + 1): Int)" => assert(h =~= ir"(x: Int) => x + x")
    }
  }
}

object HigherOrderPatternVariables {
  object Embedding extends FastANF
}
