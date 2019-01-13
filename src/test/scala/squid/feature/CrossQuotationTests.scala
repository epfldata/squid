// Copyright 2019 EPFL DATA Lab (data.epfl.ch)
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

import squid.lib.persist
import utils._

/*

TODO: the scope macro
  scope.x refers to the variable bound by x, possibly cross-quote;
    can also be a type so we can have Code[T,scope.x], slightly shorter than Code[T,scope.x.Ctx] (maybe not worth it)
  scope - x removes x from the scope

Q: can we make this work?
  def f(v: Variable[Int])(c: scope.Code[Int]) = ... // scope should refer to v...
also, alternatively:
  def f(v: Variable[Int])(c: Code[Int,scope.v]) = ...
and even, also:
  def f(scp: Scope)(c: scp.Code[Int]) = ...
called as:
  f(scope)(...)
though that's not better than just a C type parameter

*/
class CrossQuotationTests extends MyFunSuite(CrossStageDSL) {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  def foo[C](cde: Code[String,C]) = code{ ${cde} + "!" }
  
  test("Lambda-Bound") {
    
    val c0 = code{ x: Int => ${
      eqt(DSL.crossQuotation(x), code{x}.rep)
      //println(DSL.crossQuotation(x+1)) // Quasiquote Error: Cannot refer to local quoted variable 'x' from outside of quotation.
      identity(code{x + 1})
    }}
    c0 eqt code"(x:Int) => x+1"
    val f0 = c0.compile
    assert(f0(42) == 43)
    
    assertCompiles      ("code{ x: Int => ${ println( ); code{   x  } } }")
    assertDoesNotCompile("code{ x: Int => ${ println(x); code{   x  } } }")
    assertDoesNotCompile("code{ x: Int => ${ println( ); code{ %(x) } } }")
    // ^ Error: Quasiquote Error: Cannot refer to local quoted 'x' from outside of quotation.
    
    val f1 = code{ (x:Int, y:String) => ${ foo(code{y * x}) } }
    assert(f1.run.apply(3,"hey!") == "hey!hey!hey!!")
    
  }
  
  test("Val-Bound") {
    
    val c0: ClosedCode[String] = code{ val x = 42; ${
      
      foo(code{'ok.name * x})
      
    }}
    c0 eqt code{ val a = 42; 'ok.name * a + "!" }
    
    val c1: ClosedCode[String] = code{
      val x = 42;
      val y = 'ok.name
      ${ foo(code{ y * x }) }
    }
    c1 eqt code{ val a = 42; val b = 'ok.name; b * a + "!" }
    
    // Erroneous use (reported after type checking by @compileTimeOnly):
    /*
    val oops2 = 'ko
    code{oops2.name.length} alsoApply println
    */
    // ^ Error: Cross-quotation reference was never captured. Perhaps you intended to use a cross-stage-persistent reference, which needs the @squid.lib.persist annotation.
    
  }
  
  test("Crossing Several Quotation Boundaries") {
    
    val c0: ClosedCode[String => String] = code{ val x = 42; ${
      identity(code{ y: String => ${
        foo(code{ y * x }) // 'x' here refers to the one defined two levels out
      }})
    }}
    c0 eqt code{ val a = 42; (b: String) => b * a + "!" }
    
  }
  
}
