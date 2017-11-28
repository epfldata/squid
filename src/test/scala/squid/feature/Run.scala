package squid
package feature

class Run extends MyFunSuite {
  
  import TestDSL.Predef._
  
  test("New") {
    import BasicEmbedding._
    val mc = code"new MC(42)('ok, 'ko)"
    assert(mc.run == new MC(42)('ok, 'ko))
  }
  
  test("Modules") {
    same(code"List".run, List)
    same(code"Nil".run, Nil)
    same(code"Run".run, Run)
    same(code"squid.TestDSL.Predef".run.base, TestDSL)
  }
  
  test("Nullary Methods") {
    same(code"List()".run, List())
    same(code"List.empty".run, List.empty)
    same(code"List.canBuildFrom[Int]".run, List.canBuildFrom[Int])
  }
  
  test("Imperative stuff") {
    same(code"var ls: List[Int] = Nil; ls ::= 1; ls ::= 2; ls ::= 3; ls.reverse.mkString".run, "123")
    same(code"val bf = List.canBuildFrom[Int](); bf += 1; bf += 2; bf += 3; bf.result".run, List(1,2,3))
  }
  
  test("Functions") {
    
    assert(code"((x: Int) => x + 1)(42)".run == 43)
    
    val f = code"(x: Int) => x+1"
    
    assert((f.run apply 42) == 43)
    
    assert(code"Run.f(42)".run == 43)
    
  }
  
  test("Compile Error On Open Terms") {
    
    assertDoesNotCompile(""" code"($$x: Int) + 1".run """)
    
    val x = code"42": Q[Int, {val x: Int}]
    assertDoesNotCompile(""" x.run """)
    
  }
  
  test("n until m") {
    val t = code"0 until 42"
    assert(t.run == (0 until 42))
  }
  
  // FIXME more principled Constants handling
  //test("Constant Options, Seqs, Sets") {
  //  assert(ir"${Seq(Seq(1,2,3))}".run == Seq(Seq(1,2,3)), None)
  //  assert(ir"${Seq(Some(Set(1,2,3)), None)}".run == Seq(Some(Set(1,2,3)), None))
  //}
  
  test("Array and ClassTag") {
    assert(code"""Array.fill(3)("woof").toSeq""".run == Array.fill(3)("woof").toSeq)
  }
  
  test("Java Methods") {
    same(code"""String.valueOf("ok")""".run, String.valueOf("ok"))
    same(code""" "a" + "b" """.run, "ab")
    same(code""" "a" + 42 """.run, "a42")
    same(code""" "ok".length """.run, 2)
    same(code""" "ok".size """.run, 2)
  }
  
  
}
object Run {
  
  val f = (x: Int) => x + 1
  
}














