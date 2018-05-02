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

import squid.utils.meta.RuntimeUniverseHelpers
import utils.Debug._

//class PatMatTypeCoercion extends MyFunSuite(anf.SimpleANFTests.DSL) {  // <-- already does beta reduction
class PatMatTypeCoercion extends MyFunSuite {
  import DSL.Predef._
  
  test("Simple Type Coercion") {
    
    import quasi.SuppressWarning.`scrutinee type mismatch`
    
    // TODO: a way to remove the warning... without actually throwing the type info (which is being used)
    def foo[T:CodeType](x : Code[List[T],Any]) = x match {
      case code"List[$t0]($x)" => code"$x:T" // compiles
    }
    
    assertDoesNotCompile("""
    def foo[T:CodeType](x : Code[List[T],Any]) = x.erase match {  // erasure prevents subtyping knowledge to be obtained
      case code"List[$t0]($x)" => code"$x:T"
    }
    """)
    
    eqt(foo(code"List(1)").Typ, codeTypeOf[Int])
    
  }
  
  test("GADT-like Pattern Matching") {
    
    def beta[T:CodeType](x:OCode[T]): OCode[T] = x match {
      case code"((p: $t0) => $body: T)($a: t0)" => body subs ('p -> beta(a))
      case code"($f: ($t0 => T))($a)" => val (f0, a0) = (beta(f), beta(a)); code"$f($a)":OCode[T]
      case code"($p: $t0) => $body: $t1" => code"{($p) => ${beta(body)}} : T" // coercion
      case code"($a:Int) + ($b:Int)"     => code"${beta(a)} + ${beta(b)} : T" // coercion
      
      //case LeafCode(_) => x
        
      case Const(n) => Const(n)
      case base.Code((base.RepDef(h:base.Hole))) => base.Code((base.rep(h)))
      case base.Code((base.RepDef(bv:base.BoundVal))) => base.Code((base.rep(bv)))
      // ^ Should use LeafCode, but LeafCode is currently only defined for SimpleANF
    }
    
    assertCompiles("""
      def foo[T:CodeType](x:OCode[T]): OCode[T] = x match {
        case code"$x:$t2" => code"$x:T" // compiles, good
        case code"$x:Int" => code"$x:T" // compiles, good
      }
    """)
    
    assertDoesNotCompile("""
      def foo[T:CodeType](x:OCode[T]): OCode[T] = x match {
        case code"println($x:$t2)" => code"$x:T" // rejected (good) -- t2 is a different type
      }
    """)
      
    assertDoesNotCompile("""
      def foo[T:CodeType](x:OCode[T]): OCode[T] = x match {
        case code"$x:Int" => code"$x:T"
        case code"println($x:Int)" => code"$x:T" // should reject; assumption in previous case (Int<:T) should not bleed through here!
      }
    """)
    
    val model = code"(z:Int) => 42 + z"
    code"((x:Int) => (y:Int) => x+y)(42)"        neqt model
    code"((x:Int) => (y:Int) => x+y)(42)" |> beta eqt model
    
  }
  
}