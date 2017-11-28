package squid
package feature

class FreeVariablesNewSyntax extends MyFunSuite {
  
  import TestDSL.Predef._
  
  test("Simple") {
    
    import TestDSL.Quasicodes._
    
    val model = code"${base.AnyCode[Int](base.freeVar("x",typeRepOf[Int]))} + 1"
    code"(?x : Int) + 1" eqt model
    ir{(?x : Int) + 1} eqt model
    
    assertDoesNotCompile("ir{ println(?) }") // Error: Quasiquote Error: Unknown use of free variable syntax operator `?`.
    assertDoesNotCompile("ir{ println(?.selectDynamic(42.toString)) }") // Error:(18, 7) Embedding Error: Free variable introduced with `?` should have a constant literal name.
    
    // Note: old FV syntax currently still works:
    code"(x? : Int) + 1" eqt model
    code"(x?:Int)+1"     eqt model
    
  }
  
  test("Explicit Free Variables") {
    
    val x: Q[Int,{val x: Int}] = code"?x : Int"
    assert(x.rep match {
      case base.RepDef(base.Hole("x")) => true  // Note: no `base.Ascribe` node because ascriptions to the same type are removed
      case _ => false
    })
    
    val d = code"$x.toDouble" : Q[Double, {val x: Int}]
    
    val s = code"(?str : String) + $d" : Q[String, {val x: Int; val str: String}]
    
    val closed = code"(str: String) => (x: Int) => $s" : Q[String => Int => String, {}]
    val closed2 = code"(x: Int) => (str: String) => $s" : Q[Int => String => String, {}]
    
    assert(closed =~= code"(a: String) => (b: Int) => a + b.toDouble")
    assert(closed2 =~= code"(b: Int) => (a: String) => a + b.toDouble")
    
    assertDoesNotCompile(""" code"42: $$t" """) // Error:(26, 5) Embedding Error: Free type variables are not supported: '$$t'
    assertDoesNotCompile(""" code"42: t?" """)  // Error:(26, 5) Failed to parse DSL code: identifier expected but eof found.
    assertDoesNotCompile(""" code"42: ?t" """)  // Error:(40, 5) Failed to parse DSL code: identifier expected but eof found.
    
  }
  
  test("Rep extraction") {
    hopefully(code"Some(?x:Int)".rep extractRep code"Some(42)".rep isDefined)
    hopefully(code"Some(42)".rep extractRep code"Some(?x:Int)".rep isEmpty)
  }
  
  test("Term Equivalence") {
    
    assert(code"(?x: Int)" =~= code"(?x: Int)")
    assert(!(code"(?x: Int)" =~= code"(?y: Int)"))
    
    assert(code"(?x: Int)" =~= code"(?x: Int):Int")
    assert(!(code"(?x: Int)" =~= code"(?y: Int)+1"))
    assert(!(code"(?x: Int)" =~= code"(?y: String)"))
    
    assert(code"(?x: Int) + (?y: Int)" =~= code"(?x: Int) + (?y: Int)")
    
    assert(!(code"(?x: Int) + (?y: Int)" =~= code"(?y: Int) + (?x: Int)"))
    
  }
  
  test("Term Equivalence With Bindings And Free Variables") {
    
    code"val x = readInt; x + (?x: Int)" eqt code"val y = readInt; y+(?x: Int)"
    code"val x = readInt; x + (?x: Int)" neqt code"val y = readInt; (?x: Int)+(?x: Int)"
    code"val x = readInt; (?x: Int) + (?x: Int)" eqt code"val y = readInt; (?x: Int) + (?x: Int)"
    code"val x = readInt; (?x: Int) + (?x: Int)" neqt code"val y = readInt; y+(?x: Int)"
    code"val x = readInt; (?x: Int) + (?x: Int)" neqt code"val x = readInt; x+(?x: Int)"
    
  }
  
  test("Ascription and Hole Types are Checked") {
    import base.hole
    
    val N = typeRepOf[Nothing]
    
    hopefullyNot(code"?str:String" =~=  code"?str:Any")
    hopefullyNot(code"?str:String" =~= base.`internal Code`(hole("str", N)))
    
    hopefully(hole("str", N) =~=  hole("str", N))
    eqt( (hole("str", typeRepOf[Any]) extractRep hole("str", N)).get._1("str"), hole("str", N) )
    hopefullyNot(hole("str", N) =~=  hole("str", typeRepOf[Int]))
    hopefullyNot(hole("str", typeRepOf[String]) =~=  hole("str", typeRepOf[Int]))
    
  }
  
  test("Syntax: Sticking the Semi") { // These cases test the previous "new" FV syntax `x?`
    
    code"x?: Int" eqt code"$$x: Int"
    code"x?: List[Int]" eqt code"$$x: List[Int]"
    code"$$x: Int Map String" eqt
      code"x? : Int Map String"
    // Expected failure:
    //  ir"x?: Int Map String"
    // ^ this yields:
    // Error:(79, 13) Embedding Error: Quoted expression does not type check: value Map is not a member of Int
    // Warning:(79, 13) It seems you tried to annotate a free variable with `:`, but this was interpreted as operator `?:` -- use a space to remove this ambiguity.
    
    // Should raise warning: Warning:(81, 5) It seems you tried to annotate free variable `x` with `:`, which may have been interpreted as operator `?:` -- use a space to remove this ambiguity.
    assertDoesNotCompile(""" code"x?: Int Map String" """)
    assertDoesNotCompile(""" code"x?:Int Map String" """)
    
  }
  
  test("Free Variables in Patterns") {
    
    // TODO implement proper distinction between FVs and extraction holes!
    //ir"x?:Int" matches {
    //  case ir"y?: Int" => fail
    //  case ir"x?: Int" =>
    //} and {
    //  case ir"(${ir"y? : Int"}:Int)+1" => fail
    //  case ir"(${ir"x? : Int"}:Int)+1" =>
    //}
    
    val X = code"?x : Int"
    val Y = code"?y : Int"
    
    code"(?x:Int)+1" matches {
      case code"($Y:Int)+1" => fail
      case code"($X:Int)+1" => 
    } and {
      case code"(${`X`}:Int)+1" =>
    }
    
  }
  
  
}

