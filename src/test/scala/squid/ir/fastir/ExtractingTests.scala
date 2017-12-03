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
      case ir"val t = ($h: Double); println(t)" => assert(h =~= ir"42.toDouble")
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
}

object ExtractingTests {
  object Embedding extends FastANF
}
