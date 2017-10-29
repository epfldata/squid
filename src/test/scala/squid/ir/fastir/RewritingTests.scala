package squid
package ir
package fastir

class RewritingTests extends MyFunSuiteBase(BasicTests.Embedding) {
  import RewritingTests.Embedding.Predef._

  test("Worksheet") {
    val a = ir"readDouble.toInt" alsoApply println

    val b = a rewrite {
      case ir"readDouble.toInt" =>
        ir"readInt"
    } alsoApply println


  }

  test("Rewriting simple expressions only once") {
    val a = ir"println((50,60))"
    val b = a rewrite {
      case ir"($x:Int,$y:Int)" =>
        ir"($y:Int,$x:Int)"
      case ir"(${Const(n)}:Int)" => Const(n+1)
    }

    assert(b =~= ir"println((61,51))")
  }

  test("Rewriting Sequences of Bindings") {

    val a = ir"val aaa = readInt; val bbb = readDouble.toInt; aaa+bbb" alsoApply println  // FIXMElater: why isn't name 'bbb' conserved?
    val b = a rewrite {
      case ir"readDouble.toInt" =>
        ir"readInt"
    } alsoApply println

    ir"val aa = readInt; val bb = readInt; aa+bb" alsoApply println

    assert(b =~= ir"val aa = readInt; val bb = readInt; aa+bb")

//    {
//      val a = ir"val a = 11.toDouble; val b = 22.toDouble; val c = 33.toDouble; (a,b,c)"
//      val c = a rewrite {
//        case ir"val a = ($x:Int).toDouble; val b = ($y:Int).toDouble; $body: $bt" =>
//          ir"val a = ($x+$y).toDouble/2; val b = a; $body"
//      }
//      assert(c =~= ir"val a = (11+${ir"22"}).toDouble/2; val c = 33.toDouble; (a,a,c)")
//
//      /*
//      // TODO make this work like the one above
//      val d = a rewrite {
//        case ir"val a = ($x:Int).toDouble; ($y:Int).toDouble" =>
//          ir"($x+$y).toDouble/2"
//      }
//      println(d)
//      //d eqt ir"val a = (11+${ir"22"}).toDouble/2; val c = 33.toDouble; (a,a,c)"
//      */
//    }
//
//
  }


}
object RewritingTests {
  object Embedding extends FastANF
}
