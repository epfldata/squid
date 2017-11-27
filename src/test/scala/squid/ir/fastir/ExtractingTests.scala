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
      case ir"println($h)" => assert(h =~= ir"42.toDouble")
    }
    
    ir"(42, 1337)" match {
      case ir"(($l: Int), ($r: Int))" => 
        assert(l =~= ir"42")
        assert(r =~= ir"1337")
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
  }
}

object ExtractingTests {
  object Embedding extends FastANF
}
