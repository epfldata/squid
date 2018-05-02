// Copyright 2018 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package squid
package feature

import utils._

/** Demonstrating the use of OpenCode when we don't want to track context dependencies. */
class OpenCodeTests extends MyFunSuite(CrossStageDSL) {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  
  def pow(base: OpenCode[Double], exp: Int): OpenCode[Double] =
    if (exp <= 0) code"1.0"
    else code"$base * ${pow(base, exp-1)}"
  
  def foo[C](cde: Code[Double,C]) = cde
  
  test("Multi-Stage Programming") {
    
    val rd = code"readDouble"
    val model = code"$rd * ($rd * 1.0)"
    
    pow(rd, 2) eqt model
    
    val v = Variable[Double]
    val oc = pow(v.toCode, 2)
    code"{$v => $oc}" eqt code"(x:Double) => x * (x * 1.0)"
    
    oc.subs(v) ~> rd eqt model
    // ^ was: Error:(35, 24) Term of context 'squid.utils.Bottom' does not seem to have free variable 'v' to substitute.
    //   there is now a special case to consider than when using open code, it's okay if variable presence is not checked.
    
    // other valid syntaxes:
    (oc subs v) ~> rd eqt model
    oc (v) ~> rd eqt model
    
    // The main reason OpenCode is defined as Code[T,Bottom] instead of Code[T,Nothing] is that it does not mess up with type inference:
    assertCompiles("foo(oc)")
    val ocn: Code[Double,Nothing] = oc
    assertDoesNotCompile("foo(ocn)") // Error:(46, 11) type mismatch; found: Code[Double,Nothing]; required: Code[Double,C]
    assertCompiles("foo[Nothing](ocn)")
    
  }
  
  
  test("Automatic Function Lifting") {
    
    val cf = (c:ClosedCode[Int]) => Const(c.run)
    val of = (c:OpenCode[Int]) => assertDoesNotCompile("Const(c.run)") thenReturn code"$c+readInt"
    
    assertDoesNotCompile(""" code"$cf(42)" """) // Quasiquote Error: Only open code functions can benefit from automatic function lifting.
    
    code"$of(42)" eqt code"42+readInt"
    
    code"${(x:OCode[Int],y:OCode[Symbol]) => code"$y.name*$x"}(42,'ok)" eqt
      code"'ok.name*42"
    
    code"${(x:OCode[Int],y:OCode[Symbol],z:OCode[Double]) => code"$y.name*$x+$z.toString"}(42,'ok,0.5)" eqt
      code"'ok.name*42+0.5.toString"
    
    assertCompiles      ("val g: OpenCode[Int => Int] = of")
    assertDoesNotCompile("val g: ClosedCode[Int => Int] = of")
    assertDoesNotCompile("val g: OpenCode[Int => Int] = cf")
    assertDoesNotCompile("val g: ClosedCode[Int => Int] = cf")
    
  }
  
  
  val ri = Variable[() => Int]
  
  def optim[A](pgrm: OCode[A]): OCode[A] = pgrm rewrite {
    case code"List[$t]($xs*).size" => Const(xs.size)
    case code"readInt" => code"$ri()"
  }
  
  test("Open Code Rewriting and Closing") {
    
    val t0 = optim(code{
      val lss = List(1,2,3).size
      lss+1
    })
    
    t0 eqt code{val lss_x = 3; lss_x+1}
    
    assert(t0.unsafe_asClosedCode.run == 4)
    
    val t1 = optim(code{
      List(readInt,readInt).sum
    })
    
    t1 eqt code{List($(ri)(),$(ri)()).sum}
    assert(t1.close.isEmpty)
    var i = 1
    val foo = () => i alsoDo {i += 1}
    
    val t2 = code"val $ri = foo; $t1"
    same(t2.close.get, t2.unsafe_asClosedCode)
    same(t2.close.get.run, 3)
    same(i, 3)
    
  }
  
  
}
