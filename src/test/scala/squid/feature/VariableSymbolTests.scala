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

import squid.ir.BottomUpTransformer
import squid.ir.SimpleRuleBasedTransformer
import squid.utils._

class VariableSymbolTests extends MyFunSuite {
  import DSL.Predef._
  import DSL.Quasicodes._
  
  
  test("Variable Symbol Insertion & Substitution") {
    
    // Local variable
    {
      val v = new Variable[Int]
      
      var p0: Code[Int, v.Ctx] = null
      p0 = code"$v + $v"  // exact type Code[Int, v.Ctx] inferred, with proper path-dependent type on `v`
      
      assertDoesNotCompile("p0:Code[Int,Any]")
      assertCompiles("p0:Code[Int,v.Ctx]")
      
      v.substitute(p0, code"readInt") eqt code"readInt + readInt"
    }
    
    // Local object
    {
      object v extends Variable[Int]
      
      var p0: Code[Int, v.Ctx] = null
      p0 = code"$v + $v"  // exact type Code[Int, v.Ctx] inferred, with proper path-dependent type on `v`
      
      v.substitute(p0, code"readInt") eqt code"readInt + readInt"
    }
    
    // Parameter
    def test(v: Variable[Int]) {
      var p0: Code[Int, v.Ctx] = null
      p0 = code"$v + $v"  // exact type Code[Int, v.Ctx] inferred, with proper path-dependent type on `v`
      
      v.substitute(p0, code"readInt") eqt code"readInt + readInt"
    }
    test(new Variable[Int])
    
    // Tricky cases
    {
      val v = new Variable[Int]
      assertDoesNotCompile(""" code"val ${identity(v)} = 1; $v+1" """) // Error: Quasiquote Error: Inserted variable symbols can only be identifiers.
      assertDoesNotCompile(""" code"val ${v:v.type} = 1; $v+1" """) // Error: Quasiquote Error: Inserted variable symbols can only be identifiers.
      assertDoesNotCompile(""" code"val ${new base.Variable[Int]} = 1; 1+1" """) // Error: Quasiquote Error: Inserted variable symbols can only be identifiers.
      
      val p = code"123"
      assertDoesNotCompile(""" code"val $p = 0; 1" """) // Error: Quasiquote Error: Cannot insert a code value in place of a variable symbol.
      
      val n = 0
      assertDoesNotCompile(""" code"val $n = 0; 1" """) // Error: Quasiquote Error: Cannot insert object of type `Int` here.
      
      assertDoesNotCompile(""" code"val $$x = 0; $$x+1" """)
      // Warning: The `$$x` free variable syntax is deprecated; use syntax `?x` instead. (since 0.2.0)
      // Embedding Error: Quoted expression does not type check: value + is not a member of Nothing
      
      assertDoesNotCompile(""" code"var $v = 0; $v" """) // Quasiquote Error: Insertion of symbol in place of mutable variables is not yet supported; explicitly use the squid.Var[T] data type instead
      
    }
    
  }
  
  
  test("Variable Symbols in QuasiCode") {
    
    val model = code"val x = 0; x + 1"
    
    val v = new Variable[Int]
    
    val q = code{${v} + 1}
    //val q = code{${v} + 1}  // TODO enable this syntax, for consistency
    
    code{val $v = 0; ${q}} eqt model
    
    code{val $v = 0; $v + 1} eqt model
    code{val $v = 0; $v + ${q}} eqt code"val x = 0; x + (x + 1)"
    
    //code{val $(v) = 0; ${q}}
    /* ^ try to enable this syntax? (more elegant?)
         note that `val ${v} = 0` does not even parse! */
    
    code{val $v = 0; ${identity(code{$(v)+1})}} eqt model
    
    //code{val $v = 0; ${identity(code{$v + 1})}} // TODO enable this syntax, for consistency
    
  }
  
  
  test("Variable Symbol Substitution in Non-Empty Context") {
    
    val v, w = new Variable[Int]
    
    val p0: Code[Int, v.Ctx & w.Ctx] = code"$v + $w"
    
    // Notice the need for explicit type arguments here, as Scala's type inference is limited with intersections:
    v.substitute[Int, w.Ctx](p0, code"readInt") eqt code"readInt + $w"
    
  }
  
  
  test("Variable Symbol Context Capture") {
    
    val v, w = new Variable[Int]
    
    val p0 = code"$v + $w"
    
    
    // Capturing function parameters
    
    var p1: Code[Int => Int, w.Ctx] = null
    p1 = code"($v: Int) => $p0 * 2"
    p1 = code"($v => $p0 * 2)"
    p1 eqt code"(x: Int) => (x + $w) * 2"
    
    var p2: Code[Int => Int, v.Ctx] = null
    p2 = code"($w => $p0 * 2)"
    p2 = code"($w: Int) => $p0 * 2"
    p2 eqt code"(y: Int) => ($v + y) * 2"
    
    var p3: ClosedCode[(Int,Int) => Int] = null
    p3 = code"($v: Int, $w: Int) => $p0 * 2"
    p3 eqt code"(x: Int, y: Int) => (x + y) * 2"
    
    
    // Capturing local values
    
    var p4: Code[Int, w.Ctx] = null
    p4 = code"val $v: Int = 1; $p0 * 2"
    p4 = code"val $v = 1; $p0 * 2"
    p4 eqt code"val x = 1; (x + $w) * 2"
    
    p4 = code"val $v = 1; println; val $w = 2; $p0 * 2"
    p4 eqt code"val x = 1; println; val y = 2; (x + y) * 2"
    
    
    // Capturing Both
    
    var p5: Code[Int => Int, Any] = null
    p5 = code"val $v = 1; ($w => $p0 * 2)"
    p5 eqt code"val x = 1; (y: Int) => (x + y) * 2"
    
    
    // Note: capture of first-class variable symbols happens even when the variable's context is not visible in the 
    // type of the inserted term, as below:
    
    val oc: OpenCode[Int] = p0
    code"val $v = 0; println($oc)" eqt code"val x = 0; println(x + $w)"
    
    val ac: AnyCode[Int] = p0
    code"val $v = 0; println(${ac.withContext})" eqt code"val x = 0; println(x + $w)"
    
    // This can create some surprises, such as the fact that a function from Code[T,C] to Code[T,C] may end up capturing
    // a variable if the function closes over its Variable[T] instance;
    // but these surprises will never actually lead to crashes due to type mismatches or unbound variable errors.
    // To prevent these surprises, it is better to favor locally-created/or/extracted variable symbol instances over
    // global, shared ones.
    
    def foo[T:CodeType,C](p: Code[T,C]): Code[T,C] = { code"val $v = 0; $p" }
    var p: Code[Int,v.Ctx] = null
    p = foo(code"$v + 1") // this has type Code[Int,v.Ctx], but it does not actually contain any occurrences of `v`
    //v.substitute(p, fail) eqt code"val a = 0; a+1" // FIXME substitution under same binder
    
    
  }
  
  
  test("Variable Symbol Context-Aware Extraction, a.k.a. Safe Extrusion") {
    
    val u, v, w = new Variable[Int]
    
    val p0: Code[Int => Int, v.Ctx] = code"($w: Int) => ($v + $w) * 2"
    
    // TODO: allow the following syntax? (for consistency with repeated holes) – or at least raise a better error:
    //val p0 = code"($w: Int) => ($v + w) * 2"
    
    p0 matches {
      case code"($a: Int) => ($$w + a) * 2" => fail
      case code"($a: Int) => (a + ($_:Int)) * 2" => fail
      case code"($a: Int) => (($_:Int) + $$v) * 2" => fail
      case code"($a: Int) => ($$v + a) * 2" =>
        same(a, w) // this does not necessarily have to hold; but with this IR implementation, it does
    } and {
      case code"($a: Int) => ($$v + ($body:Int)) * 2" =>
        var bodyTyped: Code[Int, a.Ctx] = null
        bodyTyped = body
        body eqt code"$a"
    } and {
      //case code"($$u: Int) => ($$v + ($_:Int)) * 2" => fail  // FIXME 
      case code"($$w: Int) => ($$v + $$u) * 2" => fail 
      case code"($$w: Int) => ($$v + $$w) * 2" => // this also does not necessarily have to work, but does with this IR
    } and {
      case code"($$w: Int) => $body:Int" =>
        //body: Code[Int, w.Ctx]  // FIXME treats $w as a normal name...
    }
    
    code"(x:Int) => x+1" match {
      case code"($y:Int) => $body" =>
        // Note that `y` is refined with `OuterCtx`, which is used to refer to the context of the scrutinee (useful in `rewrite` rules)
        (y:Variable[Int]{type OuterCtx = Any}, body:Code[Int,y.Ctx])
        eqt(y.substitute(body,code"42"):Code[Int,{}], code"${code"42"}+1")
    }
    
    code"val y = 0; y+1" match {
      case code"val $z = $init:$tz; $body" =>
        (z:Variable[tz.Typ], body:Code[Int,z.Ctx])
        eqt(z.substitute(body,code"???"):Code[Int,{}], code"(??? : Int)+1")
    }
    
    code"(x:Int) => x+1" match {
      case code"($y:Int) => y+($b:Int)" =>
        assertDoesNotCompile("""b:Code[Int,Any]""")
        // ^ type mismatch; found: VariableSymbolTests.this.DSL.Code[Int,y.Ctx]; required: VariableSymbolTests.this.DSL.Predef.Code[Int,Any]
        eqt(b,code"1")
    }
    
    code"((x:Int) => x+1, (x:Int) => x+2)" match {
      case code"(($y:Int) => y+1, $rest: Int => Int)" =>
        (rest: Code[Int => Int, Any]) eqt code"($y:Int) => $y+2"
    }
    
    code"val x = 1; val y = 2; x + y" match {
      case code"val $u = 1; val $v = 2; $body" =>
        (body: Code[Int, u.Ctx & v.Ctx]) eqt code"$u + $v"
    }
    
    //base.debugFor{
    assert(captureStdErr { code"(a:Int) => (a,a)".erase match {
      case code"($x:$xt) => (x,$b:xt)" => eqt(b,code"$x")
    }} == "Term of type squid.ir.ScalaTyping.TypeHole[java.lang.String(\"xt\")] was rewritten to a term of type Int, not a known subtype.\n")
    //}
    /* The above happens because we currently implement matching of extruded variables in a hacky way (cf. doc of AST). */
    
  }
  
  
  test("Avoiding Substitution Under Same Binder") {
    
    val u, v, w = new Variable[Int]
    
    val p0 = code"(($v:Int) => $v+1, $v)"
    val p1 = v.substitute(p0,code"readInt")
    
    // FIXME: avoid substitution under same binder:
    //eqt(p1, code"(($v:Int) => readInt+1, readInt)", false)
    //eqt(p1, code"(($w:Int) => $w+1, readInt)")
    
  }
  
  
  test("Capture-Avoiding Substitution") {
    
    val u, v, w = new Variable[Int]
    
    val p0 = code"($v:Int) => $v + $w"
    val p1 = w.substitute[Int => Int, v.Ctx](p0, v.toCode)
    //eqt(p1, code"(a:Int) => a + a", false)  // FIXME
    eqt(p1, code"(a:Int) => a + $v")
    
    // FIXME? Should these really compare equal?
    eqt(code"($v:Int) => $v + $v", code"(a:Int) => a + $v")
    
  }
  
  
  test("Shadowed Variable Symbol Binding") {
    
    val v, w = new Variable[Int]
    
    val p = code"($v:Int) => ($v:Int) => $v+1"
    
    //v.substitute(p,code"readInt") eqt p  // FIXME
    
    p match {
      case code"($a:Int) => $body" =>
        body eqt code"(u:Int) => u+1"
        body eqt code"($v:Int) => $v+1"
        //a.substitute(body,code"readInt") eqt code"($v:Int) => $v+1"  // FIXME
    }
    
  }
  
  
  test("Variable Symbols in Rewritings") {
    
    val p = code"List(1,2,3).map(x => (x,x))"
    
    val q0 = p rewrite {
      case code"($a:Int) => $body:$bt" =>
        val closedBody = a.substitute[bt.Typ, a.OuterCtx](body, code"42")
        code"(y:Int) => $closedBody"
    }
    q0 eqt code"List(1,2,3).map(x => (42,42))"
    
    val q1 = p rewrite {
      case code"($a:Int) => $body:$bt" =>
        code"($a:Int) => { println($a); $body }"
    }
    q1 eqt code"List(1,2,3).map{z => println(z); (z,z)}"
    
    // Use of `OuterCtx` as well as `substitute` and `Abort()` –– ie: speculative rewriting
    code"val a = 1; val b = 2; val c = 3; val d = 4; a + c" rewrite {
      case code"val $v: $tv = $init; $body:$bt" =>
        v.substitute[bt.Typ, v.OuterCtx](body, Abort())
    } eqt code"val a = 1; val c = 3;  a + c"
    
  }
  
  
  test("Local Variable Symbols in Speculative Rewritings") {
    import squid.lib.MutVar
    
    val p = code"val a = 1; val b = 2; val c = 3; a + b + c"
    
    p rewrite {
      case code"val $v: $vt = $init; $body:$bt" =>
        val w = new Variable[MutVar[vt.Typ]]
        val newBody = v.substitute[bt.Typ, v.OuterCtx & w.Ctx](body, code"$w!")
        assertDoesNotCompile(""" code"val $w = $init; $newBody" """) // Error:(300, 10) Embedding Error: Quoted expression does not type check: type mismatch; found: vt; required: squid.lib.MutVar[vt.Typ]
        code"val $w = MutVar($init); $newBody"
    } eqt code"var a = 1; var b = 2; var c = 3; a + b + c"
    
    object R extends DSL.SelfTransformer with SimpleRuleBasedTransformer with BottomUpTransformer {
      
      rewrite {
        case code"val $v: $vt = $init; $body:$bt" =>
          val w = new Variable[MutVar[vt.Typ]]
          val newBody = v.substitute[bt.Typ, v.OuterCtx & w.Ctx](body, code"$w!")
          assertDoesNotCompile(""" code"val $w = $init; $newBody" """) // Error:(300, 10) Embedding Error: Quoted expression does not type check: type mismatch; found: vt; required: squid.lib.Var[vt.Typ]
          code"val $w = MutVar($init); $newBody"
      }
      
    }
    
     p transformWith R eqt code"var a = 1; var b = 2; var c = 3; a + b + c"
    
    
  }
  
  
  test("Interaction With Repeated Holes") {
    
    val p0 = code"((x:Int) => x+1+1, 1)"
    
    p0 match {
      case code"(($y:Int) => y+($z:Int)+($u:Int),z:Int)" =>
        same(z.run, 1)
        assertDoesNotCompile("u.run") // Error: Cannot prove that AnyRef <:< y.Ctx.
    }
    p0 match {
      case code"((y:Int) => y+($z:Int)+($u:Int),z:Int)" =>
        same(z.run, 1)
        assertDoesNotCompile("u.run") // Error: Cannot prove that AnyRef <:< Any{val y: Int}.
    }
    
  }
  
  
}
