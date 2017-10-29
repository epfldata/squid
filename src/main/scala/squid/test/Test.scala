package squid
package test

import squid.ir.FastANF

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
  // val a = ir"val a = 10.toDouble; val b = readDouble; (a + b) * 5"
  // val b = a rewrite {
  //   case dbg_ir"val x = 10.toDouble; val y = readDouble; $body(x + y)" => ir"$body(222)"
  // } alsoApply println

  //  ir"(a: Int, b: Int) => a + 1" match {
  ////    case ir"(x: Int, y: Int) => $body(y):Int" =>
  //    case db_ir"(x: Int, y: Int) => $body(x):Int" =>
  //  }

  val a = ir"(readInt + 111) * .5" rewrite {
    case ir"(($n: Int) + 111) * .5" => ir"$n * .25"
  } alsoApply println
  println(ir"readInt * .25")
  assert(a =~= ir"readInt * .25")
}
