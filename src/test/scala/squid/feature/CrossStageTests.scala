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

class CrossStageTests extends MyFunSuite(CrossStageDSL) {
  import DSL.Predef._
  
  // TODO test ref to local val, local var, local method, local type?, val/var fields and methods, this ref
  
  test("Cross-Stage References to Primitive Types Yield Constants") {
    
    def const(v:Int) = code"v"
    eqt(const(123), code"123")
    eqt(const(123), Const(123))
    eqt(CrossStage(123), Const(123))
    same(const(123).run, 123)
    
    val a = 123
    val p = code"a+1"
    same(p.toString, """code"(123).+(1)"""")
    
  }
  
  test("MSP") {
    
    val v0 = Some(123)
    val v1 = code"v0.get + 1"
    same(v1.toString, """code"((cs_0: scala.Some[scala.Int]) => cs_0.get.+(1)) % (Some(123))"""")
    val v2 = code"v1.compile + 1"
    same(v2.compile, 125)
    
  }
  
  test("Matching") {
    
    val a = 123 // will be converted to a constant
    
    code"a + 1" match {
      case code"(${CrossStage(n)}:Int)+1" => fail  // constants can no longer be interpreted as cross-stage values... could be confusing 
      case code"(${Const(n)}:Int)+1" => same(n, 123)
    }
    
    val s = 'test // not a primitive that can be converted to a constant
    
    same(code"s.name".compile, s.name)
    
    code"s.name" match {
      case code"(${Const(sym)}:Symbol).name" => fail
      case code"(${CrossStage(sym)}:Symbol).name" => same(sym, 'test)
    }
    
    val ns = new{} // non-serializable object
    assert(code"ns.toString".toString startsWith """code"((cs_0: java.lang.Object) => cs_0.toString()) % """)
    assert(code"Some(ns)".compile.x eq ns)
    
  }
  
  test("Patterns Containing Cross-Stage Values") {
    
    val ls = List(1,2,3)
    
    code"ls.size" matches {
      case code"ls.size" =>
    } and {
      case code"($l:List[Int]).size" =>
        l eqt CrossStage(ls)
    }
    
    def foo(lspat: List[Int], cde: ClosedCode[Int]) = cde match {
      case code"lspat.size" => true
      case _ => false
    }
    assert(foo(List(1,2,3), code"ls.size")) // this should not cache the pattern in `foo` (with lspat=List(1,2,3))
    assert(!foo(List(1,2), code"ls.size"))  // caching of patterns when they include a CSV is disabled
    
  }
  
  test("No Cross-Stage References Unless Allowed") {
    import TestDSL.Predef._
    
    val ls = List(1,2,3)
    assertDoesNotCompile(""" code"ls.size" """)
    // ^ Error:(77, 5) Embedding Error: Cannot use cross-stage reference: base TestDSL.Predef.base does not extend squid.lang.CrossStageEnabled.
    
  }
  
  
  test("Serialization of Cross-Stage Values") {
    
    val ls = List(1,2,3)
    val cde = code"ls.map(_+1).sum"
    
    val tree = base.scalaTree(cde.rep)
    assert(tree.toString ==
      """_root_.squid.utils.serial.deserialize("rO0ABXNyADJzY2FsYS5jb2xsZWN0aW9uLmltbXV0YWJsZS5MaXN0JFNlcmlhbGl6YXRpb25Qcm94eQAAAAAAAAABAwAAeHBzcgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwAAAAAXNxAH4AAgAAAAJzcQB+AAIAAAADc3IALHNjYWxhLmNvbGxlY3Rpb24uaW1tdXRhYmxlLkxpc3RTZXJpYWxpemVFbmQkilxjW/dTC20CAAB4cHg=").asInstanceOf[scala.collection.immutable.List[scala.Int]].map[scala.Int, scala.collection.immutable.List[scala.Int]](((x$1_0: scala.Int) => x$1_0.$plus(1)))(scala.collection.immutable.List.canBuildFrom[scala.Int]).sum[scala.Int](scala.math.Numeric.IntIsIntegral)""")
    
    same(squid.lang.IntermediateBase.toolBox.eval(tree), 2 + 3 + 4)
    
  }
  
}
