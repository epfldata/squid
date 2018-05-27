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

class CrossQuotationVariableFunctions extends MyFunSuite {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  def foo[C](cde: Code[Int,C]) = code"$cde + 1"
  
  test("Basics") {
    
    val model = code"val x = 0; (x+1) * 2"
    
    val res = code"val v = 0; ${(v:Variable[Int]) => foo(v.toCode)} * 2"
    res eqt model
    assert(res.run == 2) // res is closed!
    
    code"val v = 0; ${(v:Variable[Int]) => code"$v + 1"} * 2" eqt model
    
    //code"val v = 0; ${(v:Variable[Int]) => foo(code"42")} * 2" eqt code"val x = 0; (${code"42"}+1) * 2"
    // ^ FIXME
    
  }
  
  test("Erroneous uses") {
    
    val x = 123
    
    assertDoesNotCompile("""
      code"val v = 0; ${(x:Variable[Int]) => x.toCode} * 2"
    """)
    // ^ TODO B/E
    
    assertDoesNotCompile("""
      code"val v = 0; ${(y:Variable[Int]) => y.toCode} * 2"
    """) // Embedding Error: Quoted expression does not type check: not found: value y
    
    val fun = (v:Variable[Int]) => foo(v.toCode)
    assertDoesNotCompile("""
      code"val v = 0; ${fun} * 2"
    """)
    // ^ TODO B/E
    
    val v = Variable[Int]
    val cde = code"$v+1" // contains context of wrong variable!
    //code"val v = 0; ${(v:Variable[Int]) => cde} * 2" alsoApply println
    // ^ FIXME
    
    import scala.language.existentials
    val cde2 = { val v = Variable[Int]; code"$v+1" } // contains context of wrong variable, as existential!
    //code"val v = 0; ${(v:Variable[Int]) => cde} * 2" alsoApply println
    // ^ FIXME
    
  }
  
  test("Arities 2 and 3") {
    
    // TODO
    
    // TODO test error on arity 4
    
  }
  
}
