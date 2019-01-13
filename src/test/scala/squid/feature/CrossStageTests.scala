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

class CrossStageTests extends MyFunSuite(CrossStageDSL) {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  test("Implicit Cross-Stage Persistence of Local Variables") {
    
    @persist val field = 'ok
    @persist var mutfield = 'ok
    @persist def method(x: Int) = x + 1
    
    eqt(code"field.name" : ClosedCode[String], code"${CrossStage(field)}.name")
    eqt(code{field.name} : ClosedCode[String], code{${CrossStage(field)}.name}) // using quasicode
    
    eqt(code"mutfield.name" : ClosedCode[String], code"${CrossStage(mutfield)}.name")
    
    // could actually support this one fairly easily using a squid.lib.MutVarProxy:
    assertDoesNotCompile(""" code"mutfield = 'ko" """) // no cross-stage mutable variable update
    // ^ Error:(33, 13) Embedding Error: Unsupported feature: update to cross-stage mutable variable 'mutfield'
    
    assertDoesNotCompile(""" code"method(3)" """) // no cross-stage persistence of local methods
    // ^ Error:(30, 9) Embedding Error: Unsupported feature: Reference to local method `method`
    
  }
  
  test("Explicit Cross-Stage Persistence") {
    
    val field = 'ok
    var mutfield = 'ok
    def method(x: Int) = x + 1
    
    eqt(code"%(field).name" : ClosedCode[String], code"${CrossStage(field)}.name")
    eqt(code{%(field).name} : ClosedCode[String], code{${CrossStage(field)}.name}) // using quasicode
    
    eqt(code"%(mutfield).name" : ClosedCode[String], code"${CrossStage(mutfield)}.name")
    
    val c0 = code"%(method _)(3)"
    assert(c0.run == 4)
    
    eqt(code"%(field.name).length" : ClosedCode[Int], code"${CrossStage(mutfield.name)}.length")
    eqt(code{%(field.name).length} : ClosedCode[Int], code{${CrossStage(mutfield.name)}.length})
    
    assertDoesNotCompile(""" code"%(mutfield) = 'ko" """) // no cross-stage mutable variable update
    // ^ Error:(54, 5) Embedding Error: Quoted expression does not type check: missing argument list for method % in class Predef
    
    assertDoesNotCompile(""" code"%(method)(3)" """) // no cross-stage persistence of local methods
    // ^ Error:(55, 14) Embedding Error: Quoted expression does not type check: missing argument list for method method
    
  }
  
  val field = 'ok
  var mutfield = 'ok
  def method(x: Int) = x + 1
  type T
  
  test("Cross-Stage Persistence of Fields and Methods (via persistence of `this`)") {
    
    eqt(code"field.name" : ClosedCode[String], code"${CrossStage(this)}.field.name")
    
    eqt(code"mutfield.name" : ClosedCode[String], code"${CrossStage(this)}.mutfield.name")
    
    eqt(code"mutfield = 'ko" : ClosedCode[Unit], code"${CrossStage(this)}.mutfield = 'ko")
    
    eqt(code"method(3)" : ClosedCode[Int], code"${CrossStage(this)}.method(3)")
    
    eqt(code"Some(this)" : ClosedCode[Option[CrossStageTests]], code"Some(${CrossStage(this)})")
    
    same(code"Set.empty[T]".run, Set.empty) // note that T can be embedded here, as CrossStageTests#T
    
    object Local { type T }
    //println(dbg_code"Set.empty[Local.T]") // FIXME: uses a 'broken' type tag and crashes at runtime – we should make type tags opt-in!
    //assertDoesNotCompile(""" code"Set.empty[Local.T]" """) // no 'cross-stage persistence of type', whatever that could be
    // ^ Error:(33, 13) Embedding Error: Unknown type `CrossStageTests.this.T` does not have a TypeTag to embed it as uninterpreted.
    
  }
  
  test("Cross-Stage References to Primitive Types Yield Constants") {
    
    def const(@persist v:Int) = code"v"
    eqt(const(123), code"123")
    eqt(const(123), Const(123))
    eqt(CrossStage(123), Const(123))
    same(const(123).run, 123)
    
    val a = 123
    val p = code"%(a) + 1"
    same(p.toString, """code"(123).+(1)"""")
    
  }
  
  test("MSP") {
    
    @persist val v0 = Some(123)
    @persist val v1 = code"v0.get + 1"
    same(v1.toString, """code"((cs_0: scala.Some[scala.Int]) => cs_0.get.+(1)) % (Some(123))"""")
    val v2 = code"v1.compile + 1"
    same(v2.compile, 125)
    
  }
  
  test("Matching") {
    
    @persist val a = 123 // will be converted to a constant
    
    code"a + 1" match {
      case code"(${CrossStage(n)}:Int)+1" => fail  // constants can no longer be interpreted as cross-stage values... could be confusing 
      case code"(${Const(n)}:Int)+1" => same(n, 123)
    }
    
    @persist val s = 'test // not a primitive that can be converted to a constant
    
    same(code"s.name".compile, s.name)
    
    code"s.name" match {
      case code"(${Const(sym)}:Symbol).name" => fail
      case code"(${CrossStage(sym)}:Symbol).name" => same(sym, 'test)
    }
    
    @persist val ns = new{} // non-serializable object
    assert(code"ns.toString".toString startsWith """code"((cs_0: java.lang.Object) => cs_0.toString()) % """)
    assert(code"Some(ns)".compile.get eq ns)
    
  }
  
  test("Patterns Containing Cross-Stage Values") {
    
    @persist val ls = List(1,2,3)
    
    code"ls.size" matches {
      case code"ls.size" =>
    } and {
      case code"($l:List[Int]).size" =>
        l eqt CrossStage(ls)
    }
    
    def foo(@persist lspat: List[Int], cde: ClosedCode[Int]) = cde match {
      case code"lspat.size" => true
      case _ => false
    }
    assert(foo(List(1,2,3), code"ls.size")) // this should not cache the pattern in `foo` (with lspat=List(1,2,3))
    assert(!foo(List(1,2), code"ls.size"))  // caching of patterns when they include a CSV is disabled
    
  }
  
  test("No Cross-Stage References Unless Allowed") {
    import TestDSL.Predef._
    
    @persist val ls = List(1,2,3)
    assertDoesNotCompile(""" code"ls.size" """)
    // ^ Error:(77, 5) Embedding Error: Cannot use cross-stage reference: base TestDSL.Predef.base does not extend squid.lang.CrossStageEnabled.
    
    assertDoesNotCompile(""" code"field.name" """)
    // ^ Error:(137, 5) Embedding Error: Cannot use cross-stage reference: base TestDSL.Predef.base does not extend squid.lang.CrossStageEnabled.
    
  }
  
  test("Serialization of Cross-Stage Values") {
    
    @persist val ls = List(1,2,3)
    val cde = code"ls.map(x => x+1).sum"
    
    val tree = base.scalaTree(cde.rep)
    assert(tree.toString ==
      """_root_.squid.utils.serial.deserialize("rO0ABXNyADJzY2FsYS5jb2xsZWN0aW9uLmltbXV0YWJsZS5MaXN0JFNlcmlhbGl6YXRpb25Qcm94eQAAAAAAAAABAwAAeHBzcgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwAAAAAXNxAH4AAgAAAAJzcQB+AAIAAAADc3IALHNjYWxhLmNvbGxlY3Rpb24uaW1tdXRhYmxlLkxpc3RTZXJpYWxpemVFbmQkilxjW/dTC20CAAB4cHg=").asInstanceOf[scala.collection.immutable.List[scala.Int]].map[scala.Int, scala.collection.immutable.List[scala.Int]](((x_0: scala.Int) => x_0.$plus(1)))(scala.collection.immutable.List.canBuildFrom[scala.Int]).sum[scala.Int](scala.math.Numeric.IntIsIntegral)""")
    
    same(squid.lang.IntermediateBase.toolBox.eval(tree), 2 + 3 + 4)
    
  }
  
  
  abstract class DataManager {
    val data: Array[Int]
    // ^ Note: currently cannot make this `protected`, because the cross-stage value in `stagedIterator` is `this` instead of `data`
    //   we could prefer taking a cross-stage value to `data` instead, either always (but that may create more CS-values than
    //   necessary), or only when a this.field is bnot public 
    def iterator = data.iterator
    def stagedIterator = code"data.iterator"
  }
  
  test("Example of Data Manager Class Using CSP") {
    
    same(code"${(new DataManager{val data=Array(1,2,3)}).stagedIterator}.sum".compile, 6)
    
  }
  
}
