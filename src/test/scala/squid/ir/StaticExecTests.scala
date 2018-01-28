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

/** Due to Scala reflection problems, some of these tests may sometimes crash the compiler (and sometimes not!) */
class StaticExecTests extends FunSuite {
  
  type AST = SimpleAST
  
  def same[A](xy: (A, A)) = assert(xy._1 == xy._2)
  
  test("Constants") {

    same( staticExecAsConst[AST]{ 42 } -> 42 )
    // ie:
    same( staticExecAndSource[AST]{ 42 } )

    same( staticExecAndSource[AST]{ "ok" } )

    same( staticExecAndSource[AST]{ 'c' } )

    same( staticExecAndSource[AST]{ 'Cool.hashCode } ) // FIXME: lol, enabling this makes { "ok".take(1)+"ko" } fail

  }

  test("Basic") {

    same(staticExecAndSource[AST]{ "ok".reverse } )
    same(staticExecAndSource[AST]{ "ok".take(1)+"ko" } )
    same(staticExecAndSource[AST]{ {0 -> 1}.swap.hashCode } )

  }

  test("Bindings") {

    same(staticExecAndSource[AST]{ val x = 0; x + 1 } )
    same(staticExecAndSource[AST]{ ((x: Int) => x + 1)(42) } )
    same(staticExecAndSource[AST]{ { x: Int => x + 1}.apply(42) } )

  }
  
  ///*
  test("Variables") {
    
    same(staticExecAndSource[AST]{ lib.MutVar(0).! } ) // FIXME
    same(staticExecAndSource[AST]{ var x = ("ok" + "ko".reverse).length; x-=1; (x+=1, x, 'lol).hashCode } )
    same(staticExecAndSource[AST]{ var ls: List[Int] = Nil; ls ::= 1; ls ::= 2; ls ::= 3; ls.reverse mkString " " } )
    
  }
  
  test("By-name") {{
    
    same(staticExecAndSource[AST]{ Dummies.byNameMethod(42) })
    
    same(staticExecAndSource[AST]{ Dummies.byNameMethod(666) })
    
  }}
  
  test("Varargs") {
    
    same( staticExecAndSource[AST]{ lib.Imperative()(42) } )
    same( staticExecAndSource[AST]{ var x = 0; lib.Imperative(x += 1)(x) } )
    same( staticExecAndSource[AST]{ var x = 0; lib.Imperative(x += 1, x += 1)(x) } )
    same( staticExecAndSource[AST]{ var x = 0; val modifs = Seq(x += 1, x += 1); lib.Imperative(modifs: _*)(x) } )
    
  }
  
  test("Virtualized Constructs") {
    
    // Ascription
    same( staticExecAndSource[AST]{ (List(1,2,3) : Seq[Any]).size: Int } )
    same( staticExecAndSource[AST]{ "ok".length: Unit } )
    
    // If then else
    same( staticExecAndSource[AST]{ if (Math.PI > 0) "ok" else "ko" } )
    same( staticExecAndSource[AST]{ var x = 0; if (true) x += 1 else x += 1; x } )
    
    // While
    same( staticExecAndSource[AST]{ var x = 0; while (x < 3) { x += 1; println(x) }; x } )
    
  }
  
  test("Java") {
    
    // overloading
    same(staticExecAndSource[AST]{ "ok".indexOf('k'.toInt) })
    same(staticExecAndSource[AST]{ "ok".indexOf('k') })
    same(staticExecAndSource[AST]{ "okok".indexOf("ok") })
    same(staticExecAndSource[AST]{ "okok".lastIndexOf("ok") })
    same(staticExecAndSource[AST]{ String.valueOf(true) } )
    
    // workaround for 2-way cache compiler bug (associates java.lang.String to 'object String' instead of 'class String')
    same(staticExecAndSource[AST]{ "ok"+String.valueOf("ko") } )
    same(staticExecAndSource[AST]{ ("ko"*2) })
    same(staticExecAndSource[AST]{ ("ok" + "ko"*2).length })
    
  }
  //*/
  
  
}














