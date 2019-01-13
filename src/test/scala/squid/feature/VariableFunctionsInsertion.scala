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

import squid.ir.BottomUpTransformer
import squid.ir.SimpleRuleBasedTransformer
import squid.utils._

class VariableFunctionsInsertion extends MyFunSuite {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  def foo[C](cde: Code[Int,C]) = code"$cde + 1"
  
  test("Basics") {
    
    val model = code"val x = 0; (x+1) * 2"
    
    val res = code"val v = 0; ${(v:Variable[Int]) => foo(v.toCode)} * 2"
    res eqt model
    assert(res.run == 2) // res is closed!
    
    code"val v = 0; ${(v:Variable[Int]) => code"$v + 1"} * 2" eqt model
    
    // result of function is not existential because does not use the variable:
    code"val v = 0; ${(v:Variable[Int]) => foo(code"42")} * 2" eqt
      code"val x = 0; (${code"42"}+1) * 2"
    
    
    code"{ x: Int => ${ (x: Variable[Int]) => identity(code{ ${x} + 1 }) } }" eqt
      code"{ y: Int => y + 1 }"
    
    // Note: syntax is currently unsupported in quasicode; but there we now have cross-quotation references so it does not seems necessary
    //code{ x: Int => ${ (x: Variable[Int]) => identity(code{ ${x} + 1 }) } } alsoApply println
    
    // result of function is the WRONG existential:
    import scala.language.existentials
    val w -> cde = { val v = Variable[Int]; v -> code"$v+1" } 
    // ^ cde has type: Code[Int,v.Ctx] where val v: Variable[Int]
    var cdev = cde : (Code[Int,v.Ctx] forSome {val v: Variable[Int]})
    // cdev contains the context requirement of the wrong variable, as existential
    cdev = code"val v = 0; ${(v:Variable[Int]) => cdev} * 2"
    // ^ makes sure the context is the same; the existential context requirement was not wrongly removed
    val closed = code"val $w = 0; $cdev"
    assertDoesNotCompile("closed.run") // Error:(53, 12) Cannot prove that AnyRef <:< v.Ctx.
    assert(closed.close.get.run == 2)
    
  }
  
  test("Erroneous uses") {
    
    val x = 123
    
    assertDoesNotCompile("""
      code"val v = 0; ${(x:Variable[Int]) => x.toCode} * 2"
    """) // Quasiquote Error: Inserted variable function refers to a variable 'x' that is not bound in the scope of that quote.
    
    assertDoesNotCompile("""
      code"val v = 0; ${(y:Variable[Int]) => y.toCode} * 2"
    """) // Embedding Error: Quoted expression does not type check: not found: value y
    
    val fun = (v:Variable[Int]) => foo(v.toCode)
    assertDoesNotCompile("""
      code"val v = 0; ${fun} * 2"
    """) // Error:(71, 25) Quasiquote Error: Inserted variable functions must be lambda expressions.
    
    val v = Variable[Int]
    val cde = code"$v+1" // contains context of wrong variable!
    val res = code"val v = 0; ${(v:Variable[Int]) => cde} * 2"
    assertDoesNotCompile("res.run") // Error:(77, 9) Cannot prove that AnyRef <:< v.Ctx.
    code"val $v = 1; $res" eqt code"val a = 1; val b = 0; (a + 1) * 2"
    
  }
  
  test("Arities 2 and 3") {
    
    // TODO: support arities 2 and 3
    
    //code"val v = 0; val w = 1; ${(v:Variable[Int], w:Variable[Int]) => foo(code"$v + $w")} * 2"
    // ^ Error:(85, 69) Quasiquote Error: Inserted variable functions are currently only supported for function arity 1.
    
    assertDoesNotCompile("""
      code"val v_0 = 0; val v_1 = 1; val v_2 = 2; val v_3 = 3; ${
        (v_0:Variable[Int],v_1:Variable[Int],v_2:Variable[Int],v_3:Variable[Int]) => code"42"} * 2"
    """) // Error:(89, 5) Embedding Error: Quoted expression does not type check: overloaded method value $ with alternatives: [...]
    
  }
  
  test("Inside Rewritings") {
    
    val pgrm0 = code"println(readInt + readInt * 2)"
    
    val pgrm1 = pgrm0 rewrite {
      case code"readInt" =>
        code"val rd = readDouble; ${(rd:Variable[Double]) => foo(code"$rd.toInt")}"
    }
    pgrm1 eqt code"println({val a = readDouble; a.toInt+1} + {val a = readDouble; a.toInt+1} * 2)"
    
    pgrm1 rewrite {
      case code"val $x = readDouble; $body: $bt" =>
        code"val ri = readInt; ${(ri:Variable[Int]) => body.subs(x) ~> code"$ri.toDouble"}"
    } eqt code"println({val a = readInt; a.toDouble.toInt+1} + {val a = readInt; a.toDouble.toInt+1} * 2)"
    
  }
  
}
