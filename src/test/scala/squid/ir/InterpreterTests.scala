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
package ir

import org.scalatest.FunSuite

import MacroTesters._

class InterpreterTests extends FunSuite {
  object b extends ir.SimpleAST
  
  val Inter = new ir.BaseInterpreter
  
  def same[A](xy: (A, A)) = assert(xy._1 == xy._2)
  def runSame[A](xy: (b.Rep, A)) = {
    same(b.reinterpret(xy._1, Inter)(), xy._2)
  }
  
  test("Constants") ({
    
    runSame( shallowAndDeep(b){ 42 } )
    
    runSame( shallowAndDeep(b){ "ok" } )
    
    runSame( shallowAndDeep(b){ 'c' } )
    
    runSame( shallowAndDeep(b){ 'Cool } )
    
  })
  
  test("Basic") {/*Inter.debugFor*/{
    
    runSame( shallowAndDeep(b){ "ok".reverse } )
    runSame( shallowAndDeep(b){ "ok".take(1)+"ko" } )
    runSame( shallowAndDeep(b){ {0 -> 1} swap } )
  
  }}
  
  test("Bindings") {
    
    //runSame( shallowAndDeep(b){ (arg: {val y:Int}) => arg.y } )  // Unsupported feature: Refinement type 'AnyRef{val y: Int}'
    
    runSame( shallowAndDeep(b){ val x = 0; x + 1 } )
    runSame( shallowAndDeep(b){ ((x: Int) => x + 1)(42) } )
    runSame( shallowAndDeep(b){ {x: Int => x + 1}.apply(42) } )
    
  }
  
  test("Variables") {
    
    runSame( shallowAndDeep(b){ lib.MutVar(0) } )
    runSame( shallowAndDeep(b){ var x = ("ok" + "ko".reverse).length; x-=1; (x+=1, x, 'lol) } )
    
  }
  
  test("By-name") {{
    
    runSame( shallowAndDeep(b){ Dummies.byNameMethod(42) } )
    
    runSame( shallowAndDeep(b){ Dummies.byNameMethod(666) } )
    
  }}
  
  test("Varargs") {
    
    runSame( shallowAndDeep(b){ lib.Imperative()(42) } )
    runSame( shallowAndDeep(b){ var x = 0; lib.Imperative(x += 1)(x) } )
    runSame( shallowAndDeep(b){ var x = 0; lib.Imperative(x += 1, x += 1)(x) } )
    runSame( shallowAndDeep(b){ var x = 0; val modifs = Seq(x += 1, x += 1); lib.Imperative(modifs: _*)(x) } )
    
  }
  
  test("Virtualized Constructs") {
    
    // Ascription
    runSame( shallowAndDeep(b){ (List(1,2,3) : Seq[Any]).size: Int } )
    runSame( shallowAndDeep(b){ "ok".length: Unit } )
    
    // If then else
    runSame( shallowAndDeep(b){ if (Math.PI > 0) "ok" else "ko" } )
    runSame( shallowAndDeep(b){ var x = 0; if (true) x += 1 else x += 1; x } )
    
    // While
    runSame( shallowAndDeep(b){ var x = 0; while (x < 3) { x += 1; println(x) }; x } )
    
  }
  
  test("Java") {{
    
    // overloading
    runSame(shallowAndDeep(b){ "ok".indexOf('k'.toInt) }) 
    runSame(shallowAndDeep(b){ "ok".indexOf('k') }) 
    runSame(shallowAndDeep(b){ "okok".indexOf("ok") }) 
    runSame(shallowAndDeep(b){ "okok".lastIndexOf("ok") }) 
    runSame( shallowAndDeep(b){ String.valueOf(true) } )
    
    // workaround for 2-way cache compiler bug (associates java.lang.String to 'object String' instead of 'class String')
    runSame( shallowAndDeep(b){ "ok"+String.valueOf("ko") } )
    runSame( shallowAndDeep(b){ ("ko"*2) })
    runSame( shallowAndDeep(b){ ("ok" + "ko"*2).length })
    
  }}
  
  test("Method asInstanceOf") {
    import b.Predef._
    
    runSame(code"(42:Any).asInstanceOf[Int]+1".rep -> 43)
    
    runSame(code"('ok:AnyRef).asInstanceOf[Symbol].name".rep -> "ok")
    
    runSame(code"(1::Nil:Seq[Int]).asInstanceOf[List[Int]].isEmpty".rep -> false)
    
    // Prints a warning -- cannot interpret `isInstanceOf` directly
    //runSame(ir"(1::Nil:Seq[Int]).isInstanceOf[List[Int]]".rep -> true)
    
  }
  
  
}














