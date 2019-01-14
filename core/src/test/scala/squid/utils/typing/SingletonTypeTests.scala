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

package squid.utils.typing

import org.scalatest.FunSuite
import singleton.scope

class SingletonTypeTests extends FunSuite {
  
  val a = 0
  
  test("Singleton Types of AnyVal Types") {
    
    val x = 0
    val y = 1
    var z = 2
    
    assertCompiles      ("x: scope.x")
    assertCompiles      ("y: scope.y")
    
    assertDoesNotCompile("x: scope.y")
    assertDoesNotCompile("y: scope.x")
    // ^ Error: type mismatch; found: y.type (with underlying type Int); required: x.type
    
    assertDoesNotCompile("z: scope.z")
    // ^ Error: type mismatch; found: Int; required: z.type
    
    // With a field it does not work, for some reason (probably because we use NoPrefix for the singleType):
    //a:scope.a
    // ^ Error: type a is not a member of AnyRef{type y = y.type; type a = a.type; type x = x.type}
    
  }
  
  test("Singleton Types with Shadowing") {
    
    val x = 0
    val y = 1
    
    identity {
      val x = 1
      assertCompiles      ("x: scope.x")
      assertDoesNotCompile("x: scope.y")
    }
    
  }
  
}
