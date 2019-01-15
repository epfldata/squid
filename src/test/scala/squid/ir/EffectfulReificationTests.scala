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
package ir

object EffectfulReificationTests {
  object IR extends SimpleAST with EffectfulASTReification
}
class EffectfulReificationTests extends MyFunSuite(EffectfulReificationTests.IR) {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  test("Manual Effectful Reification") {
    
    val cde = code{ (x: Int) => ${
      import DSL._
      val r = const(42) |> registerBoundRep
      val s = c"${Code[Int,Any](r |> readVal)} * ${Code[Int,Any](crossQuotation(x))} + 1".rep |> registerBoundRep
      Code[Int,Any](s |> readVal)
    }}
    cde eqt c""" (x: Int) => {
      val r = 42
      val s = r * x + 1
      s
    }"""
    
  }
  
  test("Effectful Reification") {
    
    // Effectful reifications yield OpenCode, because there is no easy way to track their context...
    val cde: OpenCode[Int => Int] = code(x => ${
      val r = c"42".bind_!
      val s = c"$r * x + 1".bind_!
      c"println($r)".!
      c"println($s)".bind_!
      s
    })
    cde eqt c""" (x: Int) => {
      val r = 42
      val s = r * x + 1
      println(r)
      val _y = println(s)
      s
    }"""
    
  }
  
  test("Effectful Reification Without Bindings") {
    
    val ls = List(c"1", c"2", c"3")
    
    // Unrolled loop example:
    val cde: ClosedCode[Int => Int] = code{ x: Int =>
      var res = 0
      
      ${ for (e <- ls) c"res += $e * x".! }  // uses automatic convertion from () to code"()", imported from Quasicodes._
      
      println(res)
      res
    }
    cde eqt c"""{ x: Int =>
      var res = 0
      res = res + (1 * x)
      res = res + (2 * x)
      res = res + (3 * x)
      ()
      println(res)
      res
    }"""
    
    // Just for completeness, the standard alternative without effectful reification:
    import utils.typing.singleton.scope
    val cde2: ClosedCode[Int => Int] = code{ x: Int => ${
      var res: Code[Int,scope.x] = code{0}
      for (e <- ls) res = code"${res} + $e * x"
      code{
        val r = ${res}
        println(r)
        r
      }
    }}
    cde2 eqt c"""{ x: Int =>
      val res = 0 + (1 * x) + (2 * x) + (3 * x)
      println(res)
      res
    }"""
    
  }
  
}
