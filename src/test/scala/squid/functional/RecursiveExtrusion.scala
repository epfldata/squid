// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
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
package functional

import squid.utils._
import squid.utils.typing.Poly2

class RecursiveExtrusion extends MyFunSuite {
  import DSL.Predef._
  
  test("Recursive Extrusion Using First-Class Variable Symbols") {
    
    /** This function safely reverses the order of a list of let bindings, if possible. */
    def go[T:CodeType,C](p: Code[T,C])(k: Poly2[HKCodeWithCtx[C]#F] = Poly2.identity[HKCodeWithCtx[C]#F])
          : Option[Code[T,C]] = p match {
      case code"val $v: Int = $init; $body:T" =>  // FIXME this :T annotation should not be needed
        go(body)(new Poly2[HKCodeWithCtx[C & v.Ctx]#F] {
          def apply[S,D](cde: Code[S, D with C with v.Ctx]) =  // Note: Scala fails to see the override if we make it `D & C & v.Ctx`
          //code"val $v = $init; ${ k[cde.Typ,D&v.Ctx](cde.ofTyp)} : ${cde.Typ}"
          // ^ FIXME needs fix to substitution under same binder because of v.substitute call below
          { val w = Variable[Int]()
            code"val $w = $init; ${
              v.substitute[cde.Typ, D & v.Ctx & C & w.Ctx](k[cde.Typ, D & v.Ctx](cde.withUnderlyingTyp), w.toCode)
            } : ${cde.Typ}" }
        }) map { b => v.substitute[T,C](b, return None) }
      case expr => Some(k(expr))
    }
    
    assert(go( code"val a = 1; val b = 2; val c = 3; val d = 4; a + b + c + d")() 
      contains code"val d = 4; val c = 3; val b = 2; val a = 1; a + b + c + d")
    
    assert(go( code"val a = 1; val b = 2; (a+b).toDouble")() 
      contains code"val b = 2; val a = 1; (a+b).toDouble")
    
    assert(go(code"val a = 1; val b = a+1; (a+b).toDouble")() 
      isEmpty)
    
  }
  
  // TODO: similarly, test recursive rewritings with extrusion
  
}
