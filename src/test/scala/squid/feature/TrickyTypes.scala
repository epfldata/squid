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
package feature

import squid.ir.RewriteAbort
import utils._

class TrickyTypes extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Local Type Synonym") {
    
    code"Option.empty[String]" eqt {
      type String = java.lang.String
      code"Option.empty[String]"
    }
    
  }
  
  test("Local Type With Evidence") {
    
    class Lol
    
    assertDoesNotCompile("""
      code"Option.empty[Lol]"
    """)
    
    code"Option.empty[Int]" eqt {
      implicit val LolImpl = codeTypeOf[Int].asInstanceOf[CodeType[Lol]]
      code"Option.empty[Lol]"
    }
    
  }
  
  
  test("Explicit Empty Contexts and Inferred Contexts") {
    
    List[Code[Int,{}]](code"1", code"2", code"3").foldLeft(code"0") { (acc, exp) =>
      code"if ($acc != 0) $acc else $exp"
    }
    
  }
  
  
  test("Lambda with Expected Type") {
    import base.Quasicodes._
    
    val c1: Code[Int => Int => Bool => Bool,_] = code{ (s:Int) =>
      val n = 42
      k => { b => b }
    }
    
    eqt(c1.Typ, codeTypeOf[Int => Int => Bool => Bool])
    
  }
  
  
  def foo[T](x:Code[T,{}]) = code"$x==0"
  
  test("Any method called on type parameter") {
    foo(code"42") eqt code"${code"42:Any"} == 0"
    foo(code"42") neqt code"${code"42"} == 0" // Note: Int.== and Any.== have two different method symbols!!
  }
  
  test("Type evidence on non-singleton type") {
    
    eqt(foo(code"123").Typ : CodeType[_ <: Bool], codeTypeOf[Bool])
    // ^ note that this does not yield a `CodeType[Bool]` because of declaration-site variance of Code[_,C] types
    
  }
  
  
}
