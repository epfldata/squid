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

class StagingPower extends MyFunSuite {
  
  import TestDSL.Predef._
  
  def power[C](n: Int)(q: Q[Double,C]): Q[Double,C] =
    if (n == 0) code"1.0" else code"$q * ${power(n-1)(q)}"
  
  
  test("power(3)(42)") {
    
    val n = code"42.0"
    
    val p3 = power(3)(n)
    
    assert(p3 =~= code"$n * ($n * ($n * 1.0))")
    
    assert(p3.run == 42*42*42)
    
  }
  
  val model = code"(y: Double) => y * (y * (y * 1.0))"
  
  test("x => power(3)(x)") {
    
    val p3f = code"(x: Double) => ${power(3)(code"?x:Double")}" // TODO look at what this generates...
    
    assert(p3f =~= code"(x: Double) => x * (x * (x * 1.0))")
    assert(p3f =~= model)
    
    assert((p3f.run apply 2) == 8)
    
  }
  
  def power2[C](n: Int)(v: Variable[Double]): Code[Double,v.Ctx] =
    if (n == 0) code"1.0" else code"$v * ${power2(n-1)(v)}"
  
  test("power(3)(x) alternative") {
    
    val p3f = code"(x: Double) => ${(x: Variable[Double]) => power(3)(x.toCode)}"
    p3f eqt model
    
    val p3f2 = code"(x: Double) => ${(x: Variable[Double]) => power2(3)(x)}"
    p3f2 eqt model
    
  }
  
}






















