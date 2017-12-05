package squid
package ir.fastir

import squid.ir.FastANF

class ArgumentTests extends MyFunSuiteBase(ArgumentTests.Embedding) {
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
}

object ArgumentTests {
  object Embedding extends FastANF
}
