package squid
package feature

/**
  * Note: Because of the implementation, we have the same restrictions as Scala's _*
  * For example, ir"List(0, $args*)" is illegal the same way 'List(1, args:_*)' is illegal
  * It will generate the same error (in the case of QQ, *after* type-checking the deep embedding!):
  *   Error:(13, 14) no ': _*' annotation allowed here
  *   (such annotations are only allowed in arguments to *-parameters)
  *  
  *  With more effort (and support from the IR!), we could introduce the same flexibility as Scala QQ splicing, as in: q"List(0, ..$args)"
  *  
  *  Future?: allow syntax `case ir"List($xs:(Int*))`, which parses; useful when need to annotate hole type 
  */
class Varargs extends MyFunSuite {
  import TestDSL.Predef._
  
  val args = Seq(code"1", code"2", code"3")
  
  val list123 = code"List(1,2,3)"
  
  test("No splices in type position") {
    assertDoesNotCompile(""" code"Map[Int,Int]()" match { case code"Map[$ts*]()" => } """)
  }
  
  test("Simple Vararg Usage") {
    code"Seq(1,2,3)" match {
      case code"Seq[Int]($a,$b,$c)" => same(Seq(a,b,c), args)
    }
    import BasicEmbedding._
    code"new MC(42)('ok, 'ko)" match {
      case code"new MC(42)($a, $b)" =>
        eqt(a, code"'ok")
        eqt(b, code"'ko")
    }
  }
  
  test("Vararg Construction and Extraction") {
    code"List(Seq(1,2,3): _*)" matches {
      case code"List[Int]($xs*)" => fail
      case code"List[Int](${xs @ __*})" => fail
      case code"List[Int]($xs: _*)" => assert(xs == code"Seq(1,2,3)")
    }
    eqt(code"List(List(1,2,3): _*)", code"List($list123: _*)")
  }
  
  test("Spliced Unquote, Construction") {
    
    val a = code"List($args*)"
    eqt(a, list123)
    
    val b = code"List(${args: _*})"
    eqt(a, b)
    eqt(b, list123)
    
    // TODO removed this syntax (type __*)
    //val c = ir"List(${args: __*})"
    //eqt(a, c)
    //eqt(c, list123)
    
    // Note: same limitations as Scala
    //val a = dbgir"List(0,$args*)" // Error:(13, 14) no ': _*' annotation allowed here
    
    // Note: cannot splice free variables (good)
    // ir"$$xs*" // Error:(31, 6) Embedding Error: value * is not a member of Nothing
    
    val ls = List(1,2,3)
    assert(a.run == ls)
    assert(b.run == ls)
    //assert(c.run == ls)
    
    
    val args2 = Seq(code"1", code"2 + ($$x:Int)")
    val d = code"List($args2*)"
    eqt(d, code"List(1, 2 + ($$x:Int))")
    
    val d2: Q[List[Int], {val x: Int}] = d
    assertDoesNotCompile(""" d: Q[List[Int], {}] """) // Error:(73, 5) type mismatch; found: scp.TestDSL.Quoted[List[Int],Any{val x: Int}]; required: scp.TestDSL.Q[List[Int],AnyRef]
    
    // FIXME
    //val d3 = ir"List(${args2 map (r => ir"$r.toDouble")}*)"
    //eqt(d, ir"List(1 toDouble, 2 + ($$x:Int) toDouble)")
    
    val e = code"val x = 0; List($args2*)" : Q[List[Int], {}]
    eqt(e, code"val x = 0; List(1, 2 + x)")
    
  }
  
  test("Spliced Unquote, Extraction") {
    
    list123 matches {
      case code"List[Int]($xs*)" =>
        assert((xs: Seq[Q[Int,_]]) == args)
    } and {
      case code"List[Int](${xs @ __*})" =>
        assert((xs: Seq[Q[Int,_]]) == args)
    } and {
      case code"List[Int](${Seq(code"1", xs @ _*)}*)" =>
        assert((xs: Seq[Q[Int,_]]) == args.tail)
    } and {
      case code"List[Int]($xs: _*)" =>
        val seq = code"Seq(1,2,3)"
        eqt(xs, seq)
        eqt(xs.trep, seq.trep)
        eqt(xs.trep, typeRepOf[Seq[Int]])
    }
    
    val lss = code"List(Seq(1,2,3):_*)"
    lss match {
      case code"List[Int](($xs:Seq[Int]): _*)" =>
        eqt((xs: Q[Seq[Int],{}]), code"Seq(1,2,3)")
      case code"List[Int]($xs: _*)" =>
        eqt((xs: Q[Seq[Int],{}]), code"Seq(1,2,3)")
    }
    lss match {
      //case ir"List[Int](Seq($xs*):_*)" => fail // warns: Warning:(135, 12) Type inferred for hole 'xs' was Nothing. Ascribe the hole explicitly to remove this warning.
      //case ir"List[Int](Seq[Nothing]($xs*):_*)" => fail // warns: Warning:(136, 12) Type inferred for hole 'xs' was Nothing. Ascribe the hole explicitly to remove this warning.
      case code"List(Seq[Int]($xs*):_*)" =>
        assert((xs: Seq[Q[Int,{}]]) == args)
    }
    assertDoesNotCompile("""
    lss match {
      case code"List[Int](Seq($xs*:Nothing):_*)" =>
    }
    """) // Error:(104, 12) Embedding Error: Misplaced spliced hole: 'xs'
    
  }
  
  
  test("Vararg Extraction") {
    
    val seq @ Seq(x,y,z) = Seq( code"1", code"2", code"3" )
    val irSeq = code"Seq($x,$y,$z)"
    val ls = code"List($irSeq: _*)"
    
    ls match {
      //case ir"List($xs: _*)" => fail // Warning:(47, 12) Type inferred for vararg hole 'xs' was Nothing. This is unlikely to be what you want.
      case code"List[Int]($xs: _*)" => assert(xs =~= code"Seq(1,2,3)")
    }
    
    ls matches {
      //case ir"List($$seq: _*)" => // make better error?: Error:(54, 12) Embedding Error: Quoted expression does not type check: overloaded method value $ with alternatives:
         // [T, C](q: scp.TestDSL2.IR[T,C])T <and>
         // [T, C](q: scp.TestDSL2.IR[T,C]*)T
         //cannot be applied to (Seq[scp.TestDSL2.IR[Int,Any]])
      case code"List($$irSeq: _*)" =>
    } and {
      case code"List(Seq($$x,$$y,$$z): _*)" => 
    }
    
    code"List(1,2,3)" matches {
      case code"List[Int]($xs: _*)" => assert(xs =~= code"Seq(1,2,3)")
    } and {
      case code"List[Int](${xs @ __*})" => assert(xs == seq)
    } and {
      case code"List[Int]($xs*)" => assert(xs == seq)
    } and {
      case code"List($$(seq: _*))" =>
    }
    
  }
  
  test("Vararg Extraction w/ Repeated Holes") {
    
    code"List(1,2,3) -> Seq(1,2,3)" matches {
      //case ir"List[Int]($xs: _*) -> xs" => assert(xs =~= ir"Seq(1,2,3)")  // TODO aggregate type holes before lifting
      case code"List[Int]($xs: _*) -> (xs: Seq[Int])" => assert(xs =~= code"Seq(1,2,3)")
    }
    
    
  }
  
  
}

