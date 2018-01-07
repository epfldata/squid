package squid
package ir
package fastir

import scala.util.Try

class ExtractingTests extends MyFunSuiteBase(ExtractingTests.Embedding) {
  import ExtractingTests.Embedding.Predef._

  test("Matching with pure statements") {
    ir"42" match {
      case ir"$h" => assert(h =~= ir"42")
    }
    
    ir"42.toDouble" match {
      case ir"($h: Int).toDouble" => assert(h =~= ir"42")
    }
    
    ir"println(42.toDouble)" match {
      case ir"println(($h: Int).toDouble)" => assert(h =~= ir"42")
    }
    
    ir"(42, 1337)" match {
      case ir"(($l: Int), ($r: Int))" => 
        assert(l =~= ir"42")
        assert(r =~= ir"1337")
    }

    ir"val a = 10.toDouble; val b = 42.toDouble; a + b" match {
      case ir"($body: Double)" => assert(body =~= ir"val a = 10.toDouble; val b = 42.toDouble; a + b")
    }
  }
  
  test("Matching with impure statements") {
    ir"val r = readInt; r + 1" match {
      case ir"val r = ($h: Int); r + 1" => assert(h =~= ir"readInt")
    }

    assert(Try {
      ir"val r = 10.toDouble; r + 1" match {
        case ir"val rX = 42.toDouble; $body" => fail
      }
    }.isFailure)
  }
  
  test("Matching with dead-ends") {
    ir"val a = 42.toDouble; val b = a + 1; 1337" match {
      case ir"val aX = ($h1: Int).toDouble; val bX = aX + ($h2: Int); ($h3: Int)" => 
        assert(h1 =~= ir"42")
        assert(h2 =~= ir"1")
        assert(h3 =~= ir"1337")
    }

    ir"val a = 10.toDouble; val b = 20.toDouble; val c = 30.toDouble; a + b" match {
      case ir"val aX = ($a: Int).toDouble; val bX= 20.toDouble; val cX = ($c: Int).toDouble; aX + bX" =>
        assert(a =~= ir"10")
        assert(c =~= ir"30")
    }

    ir"val a = 10.toDouble; val b = 20.toDouble; val c = 30.toDouble; a + b" match {
      case ir"val bX= 20.toDouble; val aX = ($a: Int).toDouble; val cX = ($c: Int).toDouble; aX + bX" =>
        assert(a =~= ir"10")
        assert(c =~= ir"30")
    }

    // TODO better dead-end handling, should try to match dead-ends only with dead-ends?
    //ir"val a = 10.toDouble; val b = 20.toDouble; val c = 30.toDouble; a + b" match {
    //  case ir"val cX = ($c: Int).toDouble; val bX= 20.toDouble; val aX = ($a: Int).toDouble; aX + bX" =>
    //    assert(a =~= ir"10")
    //    assert(c =~= ir"30")
    //}
  }
  
  test("Extracting impure statements") {
    ir"val a = readInt; val b = readInt; a + b" match {
      case ir"val aX = readInt; val bX = readInt; aX + bX" => 
    }

    assert(Try {
      ir"val a = readInt; val b = readInt; a + b" match {
        case ir"val aX = readInt; val bX = readInt; bX + aX" => fail
      }
    }.isFailure)
    
    assert(Try {
      ir"(readInt, readDouble)" match {
        case ir"(readDouble, readInt)" => fail
      }
    }.isFailure)
    
    ir"readInt; readDouble" match {
      case ir"$a; $b" => 
        assert(a =~= ir"readInt")
        assert(b =~= ir"readDouble")
    }
    
    ir"val r1 = readInt; val a = 20 + r1; val r2 = readDouble; a + r2" match {
      case ir"val r1 = ($r1: Int); val r2 = ($r2: Double); val a = 20 + r1; a + r2" => 
        assert(r1 =~= ir"readInt")
        assert(r2 =~= ir"readDouble")
    }
    
    ir"val r1 = readInt; val a = 20 + r1; val b = r1 * 2; val r2 = a + readDouble; r2 + b" match {
      case ir"val r1 = readInt; val b = r1 * 2; val a = 20 + r1; val r2 = a + readDouble; r2 + b" => 
    }

    ir"val a = readInt; val b = readInt; b" match {
      case ir"val t = ($h: Int); val bX = readInt; bX" => assert(h =~= ir"readInt")
    }
  }
  
  test("Extracting should not match a return in the middle of block") {
    assert(Try {
      ir"val a = readInt; a + 11 + 22" match {
        case ir"val a = readInt; a + 11" => fail
      }
    }.isFailure)
  }
  
  test("Squid paper") {
    
    // 3.2
    ir"${ir"2"} + 1" match {
      case ir"($n: Int) + 1" => 
        val res = ir"$n - 1"
        assert(res =~= ir"${ir"2"} - 1")
    }
    
    // 3.6
    assert(Try {
      ir"(x: Int) => x + 1" match {
        case ir"(x: Int) => $body: Int" => fail
      }}.isFailure
    )
    
    ir"(x: Int) => x + 1" match {
      case ir"(x: Int) => $f(x): Int" => assert(f =~= ir"(x: Int) => x + 1")
    }
    // ---
  }
}

object ExtractingTests {
  object Embedding extends FastANF
}
