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

import utils.Bool

object BasicEmbedding {
  
  case class MC[A](x:Int)(syms: A*)
  
  def foo(n: Int)(s: String) = s * n
  
  
  class ClassA { outer =>
    class ClassA {
      import CrossStageDSL.Predef._
      
      def out = code"outer"
      def foo1 = code"outer.bar"
      def foo2 = code"bar"
      def bar = 0
      def runFoo = foo1.run // TODO
      
    }
    def bar = 1
  }
  
  //val clA = new ClassA // Note: does not work (widens the type, since it is not a module...)
  object clA extends ClassA
  
  object clAclA extends clA.ClassA
  
  
}
class BasicEmbedding extends MyFunSuite {
  import BasicEmbedding._
  
  import TestDSL.Predef._
  
  test("Trivial") {
    
    code"42" matches {
      case code"42" =>
    }
    code"42.toDouble + .5" matches {
      case code"42.toDouble + 0.5" =>
    }
    
  }
  
  test("Static objects and classes (java.lang.Math, String)") {
    
    val pow23 = code"Math.pow(2, 3)"
    
    pow23 match {
      case code"java.lang.Math.pow(2,3)" =>
    }
    pow23 match {
      case code"java.lang.Math.pow(${Const(2)}, ${Const(3)})" =>
    }
    pow23 match {
      case code"java.lang.Math.pow(${Const(m)}, ${Const(n)})" =>
        same(m,2)
        same(n,3)
    }
    pow23 match {
      case code"java.lang.Math.pow($m, $n)" =>
        eqt(m,code"2.0")
        eqt(n,code"3.0")
    }
    
    code"String valueOf true" matches {
      case code"java.lang.String.valueOf(true)" =>
    }
    
  }
  
  test("New") {
    
    code"new MC[Nothing](42)(???)" match {
      case code"new MC(42)()" => fail // warns NO MORE (TODO?)
      case code"new MC[Nothing](42)()" => fail
      //case ir"new MC[Nothing](42)($x)" => // warns
      case code"new MC(42)($x:Nothing)" => // warns NO MORE (TODO?)
      case code"new MC[Nothing](42)($x:Nothing)" => // ok
    }
    
    //dbg_ir"new MC(42)('ok, 'ko)" // TODO look at gen'd code and reduce
    val mc = code"new MC(42)('ok, 'ko)"
    
    mc matches {
      case code"new MC(42)('ok, 'ko)" =>
    } and {
      case code"new MC($n)('ok, Symbol($str))" =>
        eqt(n, code"42")
        eqt(str, code"${Const("ko")}")
    } and {
      //case ir"new MC($n)($a, $b)" => fail // should generate a warning
      case code"new MC[$t]($n)($a, $b)" =>
    } and {
      case code"$mc: MC[$t]" =>
        eqt(t.rep, typeRepOf[Symbol])
        eqt(mc.trep, typeRepOf[MC[Symbol]])
    }
    
    assertTypeError(""" mc match { case code"new $ab" => } """) // Embedding Error: trait ab is abstract; cannot be instantiated
    
  }
  
  test("This References (Cross-Stage Persistence)") {
    
    val aa = new clA.ClassA
    
    import CrossStageDSL.Predef._
    
    assert(aa.out =~= CrossStage(clA))
    assert(aa.out.Typ =:= codeTypeOf[ClassA])
    
    assert(aa.foo1 =~= code"${CrossStage(clA)}.bar")
    assert(aa.foo1.run == 1)
    
    assert(aa.foo2 =~= code"${CrossStage(aa)}.bar")
    assert(aa.foo2.run == 0)
    
    assert(!(aa.foo2 =~= code"${CrossStage(clAclA)}.bar"))
    assert(clAclA.foo2.run == 0)
    
  }
  
  test("Methods") {
    import collection.mutable.ArrayBuffer
    
    code"ArrayBuffer[Int](1,42,2).+=(0)" matches {
      case code"ArrayBuffer(1,$n,2).+=($m)" =>
        n eqt code"42"
        m eqt code"0"
    }
    
    code"ArrayBuffer(42).map(_+1)" matches {
      case code"ArrayBuffer[$ta]($n).map($f: ta => $tb)" => eqt(f.trep, typeRepOf[Int => Int])
    }
    
    code"ArrayBuffer[Int](42).map(_+1).isEmpty" matches {
      case code"ArrayBuffer[Int](42).map(_+1).isEmpty" => // TODO
    } and {
      case code"ArrayBuffer[$ta]($n).map($f: ta => $tb).isEmpty" =>
        eqt(ta.rep, typeRepOf[Int])
        eqt(tb.rep, typeRepOf[Int])
        eqt(f.Typ.rep, typeRepOf[Int => Int])
    }
    
  }
  
  test("Curried Functions") {
    
    val x = code"""foo(42)("ok")"""
    
    //x match { case ir"($f: Int => String)($s)" => println(f) } // nope (normal)
    
    x match {
      case code"foo($n)($s)" =>
        assert(n =~= code"42")
        assert(s =~= code""" "ok" """)
    }
    
  }
  
  test("Array's & ClassTag's") {
    code"""Array.fill(3)("woof")""".erase match {
      case code"Array.fill[String]($_)($_)($ev)" =>
        assert(ev =~= code"scala.reflect.ClassTag[String](${ Const(classOf[String]) })")
        assert(ev.run === scala.reflect.classTag[String]) // works!
        
        import scala.reflect.ClassTag /* Note: weirdly, when acribing the pattern with the scrutinee type,
          Scala does _not_ prefix ClassTag, which leads to an incompatible scrutinee type warning if this import is not made... */
        ev match {
          case code"scala.reflect.ClassTag($cls:Class[String])" => // Note: ClassTag[String] not necessary...
            eqt(cls.Typ, codeTypeOf[Class[String]])
            same(cls.run, classOf[String])
        }
        
      //case ir"Array.fill[$t]($_)($_)($ev)" =>
      // ^ Note: used to throw: Error:(131, 12) Embedding Error: Unknown type `Array[t]` does not have a TypeTag to embed it as uninterpreted.
      //   Made it:             Error:(132, 12) Embedding Error: Unsupported feature: Arrays of unresolved type.
    }
    same(code"classOf[Int]" run, classOf[Int])
    same(code"classOf[base.Quasiquotes[_]]" run, classOf[base.Quasiquotes[_]])
    // ^ Note: this generates `classOf[scp.quasi.QuasiBase$Quasiquotes]`, and funnily it seems to be valid Scala.
  }
  
  test("List, Option") {
    
    code"Some(1.2)" matches {
      //case ir"Some($_)" => fail  // warns... twice..
      case code"Some[Nothing]($_:Nothing)" => fail // equivalent to the one above, but does not generate a warning
      //case ir"Some[Any]($_)" => fail // method type args are seen as invariant (we maybe could do better but it'd require non-trivial analysis)
      case code"Some[Any]($_)" => // now method type args are seen as covariant
    } and {
      case code"Some[AnyVal]($_)" => // now method type args are seen as covariant
    } and {
      case code"Some[Double]($_)" =>
    }
    code"Option.empty: Option[Double]" match {
      //case ir"Option.empty[Double]" => fail // FIXME?
      case code"$_: Option[Double]" => 
    }
    code"Option.empty".erase match {
      //case ir"Option.empty[Double]" => fail // FIXME?
      case code"$_: Option[Double]" => 
    }
    code"Option(3.4)" match {
      case code"Option[Double]($_)" => 
    }
    
    val ls = code"List(Some(1.2),Option(3.4),Option.empty,None)"
    ls match {
      case code"List($_,$_,None,None)" => fail
      //case ir"List(Some[Any]($_),Option[Any]($_),Option.empty[Any],None)" =>
      case code"List[Option[Double]](Some[Double]($_),Option[Double]($_),($_:Option[Double]),None)" =>
    }
    ls.erase match {
      case code"$_: List[Nothing]" => fail
      case code"$_: List[AnyVal]" => fail
      case code"$_: List[Any]" =>
    }
    ls.erase match {
      case code"$ls: List[$t]" => assert(t.rep =:= typeRepOf[Option[Double]])
    }
  }
  
  
  test("Imports") {
    
    code"import scala._; List(1,2,3)" eqt code"List(1,2,3)"
    
    code"import scala.collection.mutable; mutable.ArrayBuffer(1,2,3)" eqt
           code"scala.collection.mutable         .ArrayBuffer(1,2,3)"
    
    //ir"{import scala._}; 42" eqt ir"(); 42" // warns: Warning: a pure expression does nothing in statement position; you may be omitting necessary parentheses
    code"val a = {import scala._}; 42" eqt code"42"
    
    assertDoesNotCompile(""" code"import scala._" """) // Error:(234, 13) Embedding Error: Embedded tree has no type: import scala._
    
  }
  
  
  test("Null/Default Values") {
    
    assert(nullValue[Unit] == code"()")
    assert(nullValue[Bool] == code"false")
    assert(nullValue[Char] == code"'\u0000'")
    assert(nullValue[Byte] == Const(0:Byte))
    assert(nullValue[Short] == Const(0:Short))
    assert(nullValue[Int] == code"0")
    assert(nullValue[Long] == code"0L")
    assert(nullValue[Float] == code"0F")
    assert(nullValue[Double] == code"0D")
    assert(nullValue[Null] == code"null")
    assert(nullValue[String] == code"null")
    
  }
  
  
}






