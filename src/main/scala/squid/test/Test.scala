package squid
package test

import squid.ir.FastANF
import squid.ir.fastanf.{DummyTypeRep, SplicedHole}

object Test extends App {
  object Embedding extends FastANF
  import Embedding.Predef._
  import Embedding.Quasicodes._

  //def odd(x: Int, y: Int)(z: Int)(r: Double*): Int = x + y + z
  //def foo = 42
  //
  //val bla = ir"foo"
  //
  //val program = ir"(a: Int, b: Int, c: Int, d: Double, e: Double) => odd(a, b)($bla)(d, e)"

  //val program = dbg_ir"(y: Int) => y + 5"
  //
  //println(s"$program")

  //val p1 = code"(x: Int) => x + 4"

  //case class Point(x: Int, y: Int)
  //val p = Point(0, 1)
  //
  //code{p.x} match {
  //  case code"p.x" => println(code"p.y")
  //}

  def f(args: Int*)(moreArgs: Int*) = 0

  val p = code"f(1, 2, 3)(Seq(5, 6): _*)"
  println(p)

  p match {
    case code"f($n*)($fivesix: _*)" => println((n, fivesix))
  }

  val p2 = code"(x: Int) => x + 5" alsoApply println
  p2 match {
    case code"(y: Int) => y + 5" =>
  }
}
