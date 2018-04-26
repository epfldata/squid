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

class TermRewriting extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Basics") {
    
    eqt(code"42" rewrite {
      case code"42" => code"666"
    }, code"666")
    
    eqt(code"println(42)" rewrite {
      case code"42" => code"666"
    }, code"println(666)")
    
  }
  
  test("Rewrite is Top-Down") {
    
    eqt(code"println(5)" topDown_rewrite {
      case code"${Const(n)}: Int" if n > 1 =>
        if (n % 2 == 0) code"${Const(n/2)} + ${Const(n/2)}"
        else code"${Const(n/2)} + ${Const(n/2 + 1)}"
    }, code"println { (1:Int).+(1:Int).+((1:Int).+((1:Int).+(1:Int))) }") // Ascriptions to prevent Scala from folding the constants
    
    eqt(code"List(1,2)" topDown_rewrite {
      case code"1" => code"readInt"
      case code"2" => code"readInt"
      case code"List(readInt,readInt)" => code"Nil"
    }, code"List(readInt,readInt)")
    
  }
  
  test("Captures Free Variables in Type") {
    
    val open = code"?a: Int"
    
    val r = code"List(readInt)" rewrite {
      case code"readInt" => code"$open+1"
    }
    eqt(r, code"List((?a: Int)+1)")
    r ofType[ List[Int] Code Any{val a: Int} ]()
    
  }
  
  test("Captures Unknown Context in Type") {
    
    def insert[C](x: Int Code C) = {
      var r = code"List(readInt)" rewrite { case code"readInt" => code"$x+1" }
      r = r : List[Int] Code C
      r : List[Int] Code C{val x:Int}
      assertDoesNotCompile(" r = r : List[Int] Code C{val x:Int} ")
      r
    }
    
    val r = insert(code"?a: Int")
    
    eqt(r, code"List((?a: Int)+1)")
    r ofType[ List[Int] Code Any{val a: Int} ]()
    
  }
  
  test("Aborted Rewritings") {
    
    val one = code"1"
    
    code"(1,2,3,4,5)" topDown_rewrite {
      case code"${Const(n)}: Int" =>
        if (n % 2 != 0) throw RewriteAbort("Not even!")
        code"${Const(n/2)}+${Const(n/2)}"
    } eqt code"(1, $one+$one, 3, $one+$one+($one+$one), 5)"
    
  }
  
  test("Literals in patterns") {
    
    code"'abc -> 'def" rewrite {
      case code"Symbol(${Const("abc")})" =>
        code"'lol"
    } eqt code"'lol -> 'def"
    
  }
  
  test("Non-trivial name-pattern bindings in patterns") {
    
    code"println(1.toDouble+1,2.toDouble+1)" rewrite {
      case code"(${c @ Const(n)}:Int).toDouble+1" =>
        //ir"$c.toDouble + ${Const(n+1.0)}"
        code"($c,${Const(n+1.0)})._2"
    } eqt code"println((1,2.0)._2,(2,3.0)._2)"
    
  }
  
  test("Contexts") {
    
    def foo[T,C](x:Code[T,C]):Code[T,C] = x rewrite {
      case code"val s = Symbol($str); $body:Int" =>
        // We can refer to body.Ctx as below, because Ctx is now precisely defined (not just bounded):
        identity(body) : Code[Int,body.Ctx]
        identity(body) : Code[Int,base.ContextOf[body.type]]
        // ^ identity to avoid useless statement warnings
        code"val s = Symbol($str.reverse); ${(p:Code[Symbol,body.Ctx]) => code"$body+1"}(s)"
    }
    
    foo(code"""println{val x = Symbol("ok"); (?a:Double).toInt}""") eqt
        code"""println{val x = Symbol("ok".reverse); (?a:Double).toInt+1}"""
    // Note: previous implem. used to generated a `lifted` let-binding introduced by automatic function lifting:
    //    ir"""println{val x = Symbol("ok".reverse); val lifted = x; (a?:Double).toInt+1}"""
    // But now automatic function lifting is paired with a call to tryInline, which removes that binding (good).
    
  }
  
  test("Path-dependent types in rewrite rules") {
    
    class Test { type X; def x: X = null.asInstanceOf[X] }
    
    code"42.toDouble" rewrite {
      case code"$n:Int" =>
        val x = new Test
        x.x:x.X
        val c: Code[Int,x.X] = code"42"
        code"$c+1" : Code[Int,x.X]
    }
    
    val p0 = code"List(1,2,3).map(_+1)"
    val p1 = p0 rewrite {
      case code"($v:Int)=>$body:$bt" =>
        val w = Variable[Int]()
        code"($w:Int) => ${
          body(v) ~> w.toCode alsoApply (_ eqt v.substitute[bt.Typ,v.OuterCtx with w.Ctx](body, w.toCode))
        }"
    }
    p1 eqt p0
    
    val p2 = p1 rewrite {
      case code"($v:Int)=>$body:Int" =>
        
        val w = Variable[Int]()
        /* ^ seems to work similarly with `object w extends Variable[Int]` */
        
        val newBody = code"$body + $w"
        /* ^ this part is crucial in eliciting the problematic behavior: it makes `newBody`'s type depend on `w.Ctx`,
             but then the `rewrite` macro redefines `w` and the types don't coincide anymore
             (there is currently an ad-hoc fix for this in the `rewriteImpl` macros) */
        
        code"($w:Int) => ${v.substitute[Int,v.OuterCtx with w.Ctx](newBody, w.toCode)}"
    }
    p2 eqt code"List(1,2,3).map(x=>x+1+x)"
    
  }
  
}
