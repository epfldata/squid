package squid
package feature

class Quasicode extends MyFunSuite {
  import TestDSL.Predef._
  import TestDSL.Quasicodes._
  
  test("Unquotes and Free Variables") {
    
    val a = ir{ Math.pow(2, $$('x)) }
    
    eqt(a, code"Math.pow(2, $$x)")
    
    assertDoesNotCompile("a.run") // Error:(12, 7) Cannot prove that AnyRef <:< Any{val x: Double}.
    
    val b = ir{ (x: Double) => $(a) }
    assert((b.run apply 3) == 8)
    
  }
  
  val seq @ Seq(x,y,z) = Seq( ir(1), ir(2), ir(3) )
  
  test("Vararg Insertions") {
    
    val ls = ir{ List($(x,y,z)) }
    eqt(ls, code"List($$(x,y,z))")  // remove this syntax (it can be confusing)? -- in ction $$ should be reserved for holes...
    eqt(ls, code"List(${seq: _*})")
    eqt(ls, code"List($seq*)")
    eqt(ls, ir{ List( $(seq:_*) ) })
    
  }
  
  test("Vararg Free Variables") {
    import base.$$_*
    
    //val ls = ir"List($$ls:_*)" // FIXME: Error:(33, 14) Embedding Error: Internal error: type `<error>` is erroneous...
    val ls = code"List(($$ls: Seq[Int]):_*)"
    //eqt(ls, ir"List[Int]($$ls:_*)") // FIXME: Error:(35, 13) exception during macro expansion: 
    //eqt(ls, ir{ List[Int]($$('ls):_*) }) // FIXME: Error:scala: Error: assertion failed: 
    eqt(ls, ir{ List($$[Seq[Int]]('ls):_*) })
    eqt(ls, ir{ List($$_*[Int]('ls):_*) })
    eqt(ls, ir{ List[Int]($$_*('ls):_*) })
    
  }
  
  
}


















