package squid
package ir.fastir

import utils._
import squid.ir.FastANF
import squid.ir.{SimpleRuleBasedTransformer,TopDownTransformer}

class BasicTests extends MyFunSuiteBase(BasicTests.Embedding) {
  import BasicTests.Embedding.Predef._
  
  // TODO make proper tests...
  
  test("Basics") {
    
    println(ir"(x:Int) => x.toDouble.toInt + 42.0.toInt")
    
  }
  
  test("Arguments") {
    import squid.ir.fastanf._
    
    val c0 = Constant(0)
    val c1 = Constant(1)
    val c2 = Constant(2)
    
    assert(c1 ~: c2 ~: NoArguments == ArgumentCons(c1, c2))
    assert(c0 ~~: (c1 ~: c2) ~~: NoArguments == ArgumentListCons(c0, ArgumentListCons(ArgumentCons(c1, c2), NoArguments)))
    assert(c0 ~~: (c1 ~: c2 ~: NoArguments) ~~: NoArgumentLists == ArgumentListCons(c0, ArgumentCons(c1, c2)))
    
  }
  
  test("ArgumentLists Pretty Print") {
    import squid.ir.fastanf._

    val c0 = Constant(0)
    val c1 = Constant(1)
    val c2 = Constant(2)
    val c3 = Constant(3)

    assert((c0 ~: c1).toArgssString == s"($c0, $c1)")
    assert((c0 ~~: (c1 ~: c2)).toArgssString == s"($c0)($c1, $c2)")
    assert((c0 ~~: (c1 ~: c2 ~: NoArguments)).toArgssString == s"($c0)($c1, $c2)")
    assert((c0 ~~: (c1 ~: c2 ~: SplicedArgument(c3))).toArgssString == s"($c0)($c1, $c2, $c3: _*)")
  }

  test("Transformations") {
    import squid.ir.fastanf._
    object Embedding extends FastANF
    import Embedding.Predef._
    import Embedding.Quasicodes._

    assert(Embedding.bottomUpPartial(code"42".rep){case Constant(n: Int) => Constant(n * 2)} == code"84".rep)
    //assert(Embedding.bottomUpPartial(code"(x: Int) => x + 5".rep){case Constant(5) => Constant(42)} == code"(x: Int) => x + 42".rep)
    //assert(Embedding.bottomUpPartial(code{ Some(5) }.rep){ case Constant(5) => Constant(42) } == code{ Some(42) }.rep)
    //assert(Embedding.bottomUpPartial(code"foo(4, 5)".rep){ case Constant(4) => Constant(42) } == code"foo(42, 5)".rep)

    //case class Point(x: Int, y: Int)
    //val p = Point(0, 1)
    //
    //assert(Embedding.bottomUpPartial(code{p.x + p.y}.rep){ case Constant(0) => Constant(42) } == code"p.y + p.y")
    //
    //code{p.x} match {
    //  case code"p.x" => assert(true)
    //  case _ => assert(false)
    //}
    //
    //code{p.x + p.y} match {
    //  case code"p.x" => assert(true)
    //  case _ => assert(false)
    //}

    assert(Embedding.bottomUpPartial(code"println((1, 23))".rep) { case Constant(1) => Constant(42) } == code"println((42,23))".rep)
  }

  test("Transformers") {
    //object Tr extends BasicTests.Embedding.SelfTransformer with SimpleRuleBasedTransformer with TopDownTransformer {
    //  rewrite {
    //    case ir"123" => ir"readInt + 5"
    //    case ir"readDouble" => ir"10.0"
    //  }
    //}
    //
    //val p =
    //  BasicTests.Embedding.debugFor {
    //    ir"123+readDouble+123" alsoApply println transformWith Tr alsoApply println
    //  }
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

  test("Extract") {
    import squid.ir.fastanf._
    object Embedding extends FastANF
    import Embedding.Predef._
    import Embedding.Quasicodes._

    code"42: Int" match {
      case code"${Const(x: Int)}" => assert(x == 42)
    }

    code"(x: Int) => x" match {
      case code"(x: Int) => x" =>
    }

    code"(x: Int, y: Int) => x + 1 + y" match {
      case code"(y: Int, z: Int) => y + 1 + z" => assert(true)
      case _ => assert(false)
    }

    //case class Point(x: Int, y: Int)
    //val p = Point(0, 1)
    //
    //code{p.x} match {
    //  case code"p.x" => assert(true)
    //  case _ => assert(false)
    //}
    //
    //code{p.x + p.y} match {
    //  case code"p.x" => assert(true)
    //  case _ => assert(false)
    //}
  }

}
object BasicTests {
  object Embedding extends FastANF
}
