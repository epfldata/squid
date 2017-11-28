package squid
package feature

class Antiquotation extends MyFunSuite {
  import TestDSL.Predef._
  import TestDSL.Quasicodes._
  
  val n = code"42"
  
  test("Term Unquote") {
    
    eqt(code"$n.toDouble + $n : Double", code"42.toDouble + 42")
    
  }
  
  test("Type Unquote") {
    
    val t = TestDSL.`internal CodeType`[Int](typeRepOf[Int])
    code"(42,43)".erase match {
      case code"($x: $$t, $y:$s)" =>
        subt(x.trep, typeRepOf[Int])
        subt(x.trep, s.rep)
    }
    
  }
  
  test("Escaped Term Unquote") {
    
    code"(42,42)".erase match {
      case code"($$n, $m: Int)" => eqt(m, n)
    }
    code"println(42)" match {
      case code"println($$n)" =>
    }
    
    assertDoesNotCompile(""" code"$$" """) // scp.quasi.EmbeddingException: Empty escaped unquote name: '$$'
    
  }
  
  test("Escaped Type Unquote") {
    
    eqt(code"Option.empty[String]", code"scala.Option.empty[String]")
    
    code"scala.Option.empty[Int]".erase match {
      case code"scala.Option.empty[$t]" =>
        eqt(t.rep, typeRepOf[Int])
        code"Option.empty[String]" matches {
          case code"scala.Option.empty[$$t]" => fail
          case code"scala.Option.empty[$t]" => eqt(t.rep, typeRepOf[String])
        }
        code"Option.empty[Int]" matches {
          case code"scala.Option.empty[$$t]" =>
        }
    }
    
  }
  
  test("Alternative Unquote Syntax") { // Note: probably never useful; rm syntax?
    
    val (x,y) = (code"1", code"2")
    
    assertDoesNotCompile(""" code"println($$(x,y))" """) // Error:(68, 5) Quasiquote Error: Vararg splice unexpected in that position: $(x, y)
    
    assertDoesNotCompile("""
      code"println(1,2)" match {
        case code"println($$(x,y))" =>
      }
    """) // Error:(64, 12) Quasiquote Error: Vararg splice unexpected in that position: $(x, y)
    
    eqt(ir{List(${Seq(x,y):_*})}, code"List(1,2)")
    eqt(code"List($$(x,y))", code"List(1,2)")
    
    val seq = Seq(x,y)
    
    assertDoesNotCompile(""" ir{println($(seq:_*))} """) // Error:(87, 7) Quasiquote Error: Vararg splice unexpected in that position: ((seq): _*)
    assertDoesNotCompile(""" code"println(${seq:_*})" """) // Error:(87, 7) Quasiquote Error: Vararg splice unexpected in that position: ((seq): _*)
    
    eqt(code"($$x:Int)+$x", code"($$x:Int)+1")
    
    assert(code"($$x:Int, $$y:Int)".rep.extractRep(code"(1,2)".rep).get._1 === Map("x" -> code"1".rep, "y" -> code"2".rep))
    assert(code"( $x,      $y    )".rep.extractRep(code"(1,2)".rep).get._1 === Map())
    
    code"List(1,2)" match { case code"List($$(x,y))" => }
    
    
    val p = code"println(1,2)"
    assertDoesNotCompile(""" p match { case code"println($$(x,y))" => } """) // Error:(147, 12) Quasicode Error: Vararg splice unexpected in that position: $(x, y)
    assertDoesNotCompile(""" p match { case code"println($$(seq:_*))" => } """)
    p match { case code"println($$x,$$y)" => }
    
    var count = 0
    
    code"$${count += 1; ir{42}}" matches {
      case code"$${count += 1; x}" => fail
      case code"$${count += 1; n}" =>
    } and {
      case code"$${count += 1; ir{42}}" =>
    }
    
    assertDoesNotCompile(""" (??? : Code[Int,_]) match { case code"$${count += 1; $m}" => } """) // Error:(159, 36) Quasiquote Error: Illegal hole position for: $m
    
    assert(count == 4)
    
  }
  
}



