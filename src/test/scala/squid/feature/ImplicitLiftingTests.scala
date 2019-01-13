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
import squid.utils._

class ImplicitLiftingTests extends MyFunSuite(CrossStageDSL) {
  import CrossStageDSL.Predef._
  import CrossStageDSL.ImplicitLifting._
  
  test("Simple Implicit Lifting") {
    
    implicitly[ClosedCode[Ordering[Int]]] eqt
      c"scala.math.Ordering.Int"
    
    implicitly[ClosedCode[Ordering[Int -> Int]]] eqt
      c"scala.math.Ordering.Tuple2[scala.Int, scala.Int](scala.math.Ordering.Int, scala.math.Ordering.Int)"
    
  }
  
  class MyClass
  
  test("Cross-Stage Implicit Lifting") {
    
    @persist implicit val ev: Ordering[MyClass] = Ordering.by(_.hashCode) // local instance value
    
    val ordCde = implicitly[ClosedCode[Ordering[MyClass]]]
    ordCde eqt c"ev" // cross-stage persistence
    assert(ordCde.run == ev)
    
    implicitly[ClosedCode[Ordering[MyClass -> MyClass]]] eqt
      c"math.Ordering.Tuple2(ev,ev)"
    
  }
  
}
