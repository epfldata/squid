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

import utils.Debug._

class Matching extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Holes") {
    val q = code"0 -> 'ok"
    q match {
      //case ir"0 -> $b" => fail // Warning:(11, 12) Type inferred for hole 'b' was Nothing. Ascribe the hole explicitly to remove this warning.
      case code"0 -> ($b: Symbol)" => eqt(b, code"'ok")
    }
    
    code"$q -> $q "
    assertDoesNotCompile(""" code"$q // $q " """) // Error:(15, 5) Quasiquote Error: Illegal hole position for: $q
    assertDoesNotCompile(""" code"0 -> 'ok // $q " """) // Error:(15, 5) Quasiquote Error: Illegal hole position for: $q
    assertDoesNotCompile(""" code"0 -> 'ok // ${Const(42)} " """) // Error:(15, 5) Quasiquote Error: Illegal hole position for: ${TestDSL2.Predef.Const.apply[Int](42)(...)}
    assertDoesNotCompile(""" q match { case code"0 -> 'ok // $x " => } """) // Error:(15, 20) Quasiquote Error: Illegal hole position for: $x
  }
  
  test("Shadowing") {
    
    val q = code"(x:Int) => (x:String) => x"
    q.erase match {
      case code"(y:Int) => $b: $t" =>
        eqt(t.rep, typeRepOf[String => String])
        eqt(b: Q[_, {val y: Int}], code"(z: String) => z")
    }
    
  }
  
  test("Type Ascription") {
    
    (code"42": Q[_,_]) match {
      case code"$x: Double" => ???
      case code"$x: Int" =>
        assert(x === code"42")
    }
    
    val n = code"42"
    val m = code"42:Int"
    assert(n =~= m)
    assert(code"$n * $m" =~= code"$m * $n")
    
    assert(code"(x: Int) => x + $n" =~= code"(x: Int) => x + $m")
    
    code"42" eqt code"42: Int"
    code"42" eqt code"42: Any"
    
  }
  
  test("Methods") {
    
    code"42.toDouble" match {
      case code"($x: Int).toDouble" =>
        assert(x =~= code"42")
    }
    
    val t = code"42.toDouble"
    val s = code".5 * $t"
    
    s match {
      case code"($a: Double) * ($b: Double)" =>
        assert(a =~= code"0.5")
        assert(b =~= code"42.toDouble")
    }
    
    code" ??? " match { case code" ??? " => }
    
    code"((x: Int) => println(x): Any)(0)" eqt code"((x: Int) => println(x): Any)(0)"
    
  }
  
  test("Free Variables") {
    
    //assert(ir"$$x" =~= ir"$$x") // Warning:(66, 12) Type inferred for hole 'x' was Nothing. Ascribe the hole explicitly to remove this warning.
    assert(code"?x:Nothing" =~= code"?x:Nothing")
    assert(code"?x:Int" =~= code"?x:Int")
    assert(code"(?x:Int)+1" =~= code"(?x:Int)+1")
    
  }
  
  test("Construction Unquotes in Extractors") {
    
    val x = code"42"
    code"(42, 666)" match {
      case code"($$x, 666)" => 
    }
    
    /*
    // Note: the following syntax is not special-cased (but could be):
    val xs = Seq(ir"1", ir"2")
    ir"List(1, 2)" match {
      case ir"($$xs*)" => 
    }
    */
  }
  
  test("Nominal and Extracted Binders") {
    
    val p = code"val x = 42; x + 1"
    
    p match {
      case code"val y: Int = $v; $b" =>
        
        val y = code"?y: Int"
        
        var t : Int Code Any{val y: Int} = null
        t = b // 'b' has ^ this exact type
        t = y // 'y' has ^ this exact type
        
        eqt(b, code"$y + 1") // 'b' has a FV equivalent to 'y'
        eqt(b, code"(?y:Int) + 1")
        //b match { case code"$$y + 1" => } // FIXME this syntax 
        b match { case code"(${`y`}:Int) + 1" => } // TODO infer type from pattern type... 
        b match { case code"(${`y`}:Int) + ($c: Int)" => eqt(c, code"1") }
        code"readInt + 1" match { case code"(${`y`}:Int) + 1" => fail  case code"($y:Int) + 1" => eqt(y, code"readInt") }
        
        val newB = code"$y + 2"
        newB match { case code"(${`y`}:Int) + 2" => }
        
    }
    
    p match {
      case code"val $y: Int = $v; $b" =>
        
        var yt : Int Code y.Ctx = null
        yt = y.toCode // 'y.toCode' has ^ this exact type
        
        eqt(y, code"?y: Int", false) // 'y' is not a mere hole/FV, it's a term that will only extract exactly the corresponding original binder
        eqt(b, code"$y + 1") // 'b' really has a FV instead of a bound reference to 'y'
        eqt(b, code"(?y:Int) + 1", false)
        b match { case code"$$y + 1" => } // but the FV in 'b' remebers its original binder 
        b match { case code"$$y + ($c: Int)" => eqt(c, code"1") }
        code"readInt + 1" match { case code"$$y + 1" => fail  case code"($y:Int) + 1" => eqt(y, code"readInt") }
        
        val newB = code"$y + 2"
        newB match { case code"$$y + 2" => }
        
    }
    
    code"(x: Int) => x + 1" match {
      case code"($y: Int) => $b" =>
        b match { case code"$$y + 1" => }
    }
    
    assertDoesNotCompile(""" (??? : Code[Int,{}]) match { case code"val _ = $v: Int; $b" => } """) // Error:(129, 38) Quasiquote Error: All extracted bindings should be named.
    //assertDoesNotCompile(""" (??? : IR[Int=>Int,{}]) match { case ir"(_: Int) => $b: Int" => } """) // Error:(129, 42) Quasiquote Error: All extracted bindings should be named.
    
  }
  
  test("Advanced Extracted Binders") {
    import base._
    
    val q = code"val x = 42; x + 1"
    
    q match {
      case code"val ${y @ AnyCode(RepDef(bv @ BoundVal(name)))}: $t = $v; $b" =>
        same(name, "x")
        //eqt(bv.typ, constType(42)) // No more the case -- now the type of let bindings is not narrowed from the value in ModularEmbedding
        eqt(bv.typ, typeRepOf[Int])
    }
    
    //assertDoesNotCompile(""" q match { case ir"val ${IR(t)}: Int = $v; $b" => } """) // Error:(132, 20) Quasiquote Error: All extracted bindings must be named. In: ${IR((t @ _))}
    
  }
  
  /*test("Extracted Binders for Multi-Parameter Lambdas") { // TODO
    
    ir"(a: Int, b: Int) => a+b" match {
      case ir"($x: Int, $y: Int) => $b" =>
        show(x,y)
    }
    
  }*/
  
  test("Extraction with null and ???") {
    import base._
    
    code"val str: String = null; str.length" matches {
      case code"val str: String = $v; $body: Int" =>
        v eqt code"null"
    } and {
      case code"val str: $t = $v; $body: Int" =>
        //eqt(t, irTypeOf[String])
        // ^ Not working because of mergign of -String with +Null(null) from the arg; cf. ScalaTyping 
        eqtBy(t, codeTypeOf[String], false)(_ =:= _)
    } and {
      case code"val ${x @ AnyCode(RepDef(bv:BoundVal))}: $t = $v; $body: Int" =>
        eqt(bv.typ, typeRepOf[String]) // Not working because of mergign of -String with +Null(null) from the arg; cf. ScalaTyping 
    }
    
    code"val str: String = ???; str.length" matches {
      case code"val str: String = $v; $body: Int" =>
        v eqt code"???"
    } and {
      case code"val str: $t = $v; $body: Int" =>
        //eqt(t, irTypeOf[String])
        // ^ Not working because of mergign of -String with +Null(null) from the arg; cf. ScalaTyping 
        eqtBy(t, codeTypeOf[String], false)(_ =:= _)
    } and {
      case code"val ${x @ AnyCode(RepDef(bv:BoundVal))}: $t = $v; $body: Int" =>
        eqt(bv.typ, typeRepOf[String]) // Not working because of mergign of -String with +Null(null) from the arg; cf. ScalaTyping 
    }
    
  }
  
  
  test("Extractor Caching Indexes on Types Properly") {
    
    def matchTyp[T:CodeType](x:Code[Any,{}]) = {
      val t = implicitly[CodeType[T]]
      x match {
        case code"$x:Nothing" => fail
        case code"($x:Nothing,$y:Nothing)" => fail
        case code"$x:T" => 1
        case code"$x:$$t" => 2 
        case code"($x:T,$y:T)" => 3
        case code"$x:Any" => 4
      }
    }
    
    assert(matchTyp[Int](code"42") == 1)
    assert(matchTyp[Symbol](code"'ko") == 1)
    assert(matchTyp[Symbol](code"42") == 4)
    assert(matchTyp[Symbol](code".5") == 4)
    assert(matchTyp[Symbol](code"'ko") == 1)
    assert(matchTyp[Double](code".5") == 1)
    assert(matchTyp[Int](code"(1,2)") == 3)
    assert(matchTyp[Boolean](code"(1,2)") == 4)
    assert(matchTyp[Boolean](code"(true,false)") == 3)
    
    
    
    def matchTyp2(x:Code[Any,{}], t: CodeType[_]) = x match {
      case code"$x:$$t" =>
      case _ => fail
    }
    
    matchTyp2(code"42", codeTypeOf[Int])
    matchTyp2(code"'ok", codeTypeOf[Symbol])
    
    
  }
  
  
}

class LegacyMatching extends MyFunSuite(LegacyTestDSL) {
  import DSL.Predef._
  
  test("Extracted Binders") {
    
    code"val x = 42; x + 1" match {
      case code"val $y0: Int = $v; $b" =>
        /* ^ LegacyTestDSL will extrude `b` the old way, by substituting references to y0 with holes (that have memory) */
        
        val y = y0.toCode.asInstanceOf[Code[Int,Any{val y:Int}]]
        /* ^ the QQ macro used to extract such a term, with this type */
        
        // (???) Note:
        //y [ Int IR Any{val y: Int} ] // Error:(95, 19) No TypeTag available for scp.TestDSL2.IR[Int,Any{val y: Int}]
        
        var yt : Int Code Any{val y: Int} = null
        yt = y // 'y' has ^ this exact type

        eqt(y, code"?y0: Int", false) // 'y' is not a mere hole/FV, it's a term that will only extract exactly the corresponding original binder
        eqt(b, code"$y + 1", false) // 'b' really has a FV instead of a bound reference to 'y'
        eqt(b, code"(?y0:Int) + 1")
        b match { case code"$$y + 1" => } // but the FV in 'b' remebers its original binder 
        b match { case code"$$y + ($c: Int)" => eqt(c, code"1") }
        code"readInt + 1" match { case code"$$y + 1" => fail  case code"($y:Int) + 1" => eqt(y, code"readInt") }

        val newB = code"$y + 2"
        newB match { case code"$$y + 2" => }
        
    }
    
    code"(x: Int) => x + 1" match {
      case code"($y0: Int) => $b" =>
        val y = y0.toCode.asInstanceOf[Code[Int,Any{val y:Int}]]
        b match { case code"$$y + 1" => }
    }
    
  }
  
}











