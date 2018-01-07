package squid
package ir
package fastir

class RewritingTests extends MyFunSuiteBase(RewritingTests.Embedding) {
  import RewritingTests.Embedding.Predef._
  import RewritingTests.Embedding.Quasicodes._

  test("Simple rewrites") {
    val a = ir"123" rewrite {
      case ir"123" => ir"666"
    }
    assert(a =~= ir"666")

    val b = ir"42.toFloat" rewrite {
      case ir"42.toFloat" => ir"42f"
    }
    assert(b =~= ir"val t = ${ir"42"}.toFloat; 42f")

    val c = ir"42.toDouble" rewrite {
      case ir"(${Const(n)}: Int).toDouble" => ir"${Const(n.toDouble)}"
    }
    assert(c =~= ir"val t = ${ir"42"}.toDouble; 42.0")
  }

  test("Rewriting subpatterns") {
    val a = ir"(10.toDouble + 111) * .5" rewrite {
      case ir"(($n: Double) + 111) * .5" => ir"$n * .25"
    }
    assert(a =~= ir"val t = 10.toDouble; val t2 = (t + 111) * .5; t * .25")

    val b = ir"Option(42).get" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(b =~= ir"val t = Option(42).get; 42")

    val c = ir"val a = Option(42).get; a * 5" rewrite {
      case ir"Option(($n: Int)).get" => n
      case ir"($a: Int) * 5" => ir"$a * 2"
    }
    assert(c =~= ir"val t1 = Option(42); val t2 = t1.get; val t3 = ${ir"42"} * 5; ${ir"42"} * 2")

    val d = ir"val r = (() => readInt.toDouble)(); r * r" rewrite {
      case ir"readInt.toDouble" => ir"readDouble"
    }
    assert(d =~= ir"val r = (() => readDouble)(); r * r")
  }
  
  test("Rewriting with dead-ends") {
    val a = ir"Option(42).get; 20" rewrite {
      case ir"Option(($n: Int)).get; 20" => n
    }
    assert(a =~= ir"val t = ${ir"Option(42)"}; 42")
    
    val b = ir"val r1 = readDouble.toInt; val a = r1 + 2; val b = r1 + 4; r1" rewrite {
      case ir"readDouble.toInt" => ir"readInt"
      case ir"2" => ir"4"
      case ir"4" => ir"8"
    }
    assert(b =~= ir"val r1 = readInt; val a = r1 + 8; val b = r1 + 8; r1")
    
    val c = ir"val r1 = readInt; val f = (x: Int) => { val r2 = readInt; val a = x + 1; r2 }; f(r1)" rewrite {
      case ir"(x: Int) => { val rX = readInt; val a = x + 1; rX }" =>  ir"(x: Int) => { val a = x + 22; x }"
    }
    assert(c =~= ir"val r1 = readInt; val f = (x: Int) => { val a = x + 22; x }; f(r1)")
  } 
  
  test("Substitution should be called from inside a reification context") {
    val a = ir"readDouble" rewrite {
      case ir"readDouble" => ir"42.toDouble"
    }
    assert(a =~= ir"42.toDouble")
  }
  
  test("Code generation should handle a hole in return position") {
    val a = ir"val a = 10.toDouble; val b = 22.toDouble; a + b" rewrite {
      case ir"val a = 10.toDouble; ($body:Double)" => ir"readDouble"
    }
    assert(a =~= ir"readDouble")
  }
  
  test("Rewriting sequences of bindings") {
    val a = ir"val a = readInt; val b = readDouble.toInt; a + b" rewrite {
      case ir"readDouble.toInt" => ir"readInt"
    }
    assert(a =~= ir"val a = readInt; val b = readInt; a + b")
  }
  
  test("Rewriting with HOPHoles") {
    val a = ir"val a = 11.toDouble; val b = 22.toDouble; val c = 33.toDouble; (a,b,c)" rewrite {
      case ir"val a = ($x:Int).toDouble; val b = ($y:Int).toDouble; ($body(a, b): Tuple3[Double, Double, Double])" =>
        ir"val a = ($x+$y).toDouble/2; $body(a, a)"
    }
    val f = ir"(x: Double, y: Double) => (x, y, 33.toDouble)"
    assert(a =~= ir"val a = (11+${ir"22"}).toDouble/2; $f(a, a)")
  }
  
  test("Rewriting lambdas") {
    val a = ir"val a = 11.toDouble; val f = (x: Double) => x * 2; f(a)" rewrite {
      case ir"(x: Double) => x * 2" => ir"(x: Double) => x * 4"
    }
    assert(a =~= ir"val a = 11.toDouble; val fOld = (x: Double) => x * 2; val f = (x: Double) => x * 4; f(a)")

    // Rewrite multiple lambdas
    val b = ir"val a = 11.toDouble; val f1 = (x: Double) => { println(x); x * 2 }; val f2 = (x: Double) => { val t = x * 2; val p = println(x); t }; f1(a) + f2(a)" rewrite {
      case ir"(x: Double) => { println(x); x * 2 }" => ir"(x: Double) => x * 4"
    }
    assert(b =~= ir"val a = 11.toDouble; val f1 = (x: Double) => x * 4; val f2 = (x: Double) => x * 4; f1(a) + f2(a)")
    
    // Rewrite nested lambda
    val c = ir"val a = 11.toDouble; val f1 = (x: Double) => { val f2 = (x: Double) => { val t = x * 2; val p = println(x); t }; println(x); f2(x) * 2 }; f1(a)" rewrite {
      case ir"(x: Double) => { println(x); x * 2 } " => ir"(x: Double) => x * 4"
    }
    assert(c =~= ir"val a = 11.toDouble; val f1 = (x: Double) => { val f2 = (x: Double) => x * 4; println(x); f2(x) * 2 }; f1(a)")
    
    val d = c rewrite {
      case ir"(x: Double) => { println(x); val f = (x: Double) => x * 4; f(x) * 2 }" => ir"(x: Double) => x * 4"
    }
    assert(d =~= ir"val a = 11.toDouble; val f = (x: Double) => x * 4; f(a)")
  }
  
  test("Rewriting should happen at all occurences") {
    val a = ir"val a = Option(11).get; val b = 22; val c = Option(33).get; a + b + c" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(a =~= ir"val a = Option(11).get; val b = 22; val c = Option(33).get; ${ir"11"} + 22 + 33")
    
    val b = ir"val a = Option(Option(11).get).get; val b = 22; a + b" rewrite {
      case ir"Option(($n: Int)).get" => n
    }
    assert(b =~= ir"val t1 = Option(11).get; val t2 = Option(11).get; ${ir"11"} + 22")
  }
  
  test("Rewriting should remove the dependent pure statements") {
    val a = ir"val a = readInt; val b = readDouble.toInt; a + b" rewrite {
      case ir"readDouble.toInt" => ir"readInt"
    }
    assert(a =~= ir"val a = readInt; val b = readInt; a + b")
  }
  
  test("Rewriting should not remove statements that are part of the result") {
    val a = ir"val a = readInt; val b = readDouble; a + b" rewrite {
      case ir"readInt" => ir"readDouble.toInt"
    }
    assert(a =~= ir"val a = readDouble.toInt; val b = readDouble; a + b")
  }
  
  test("Rewriting should not partially match inside a lambda") {
    val a = ir"(x: Double) => x * 2 + 33" rewrite {
      case ir"(x: Double) => x * 2" => fail
    }
  }
  
  test("Rewriting should generate ANF valid code") {
    val a = ir"List(1,2,3).foldLeft(0)((acc,x) => acc+x) + 4" rewrite {
      case ir"($ls: List[Int]).foldLeft[Int]($init)($f)" =>
        ir"var cur = $init; $ls.foreach(x => cur = $f(cur, x)); cur"
    }
    assert(a =~=
      ir"val t = List(1, 2, 3); val f = ((acc: Int, x: Int) => acc+x); t.foldLeft(0)(f); var cur = 0; t.foreach(x => cur = f(cur, x)); cur + 4")

    val b = ir"4 + List(1,2,3).foldLeft(0)((acc,x) => acc+x)" rewrite {
      case ir"($ls: List[Int]).foldLeft[Int]($init)($f)" =>
        ir"var cur = $init; $ls.foreach(x => cur = $f(cur, x)); cur"
    }
    assert(b =~=
      ir"val t = List(1, 2, 3); val f = ((acc: Int, x: Int) => acc+x); t.foldLeft(0)(f); var cur = 0; t.foreach(x => cur = f(cur, x)); 4 + cur")
  }
  
  test("Rewriting a by-name argument rewrites inside it") {
    import RewritingTests.f
    
    val a = ir"f({val a = 10.toDouble; println(10.toDouble); a})" rewrite {
      case ir"10.toDouble" => ir"42.toDouble"
    }
    assert(a =~= ir"f({val a = 10.toDouble; println(42.toDouble); val b = 10.toDouble; 42.toDouble})")
  }
  
  test("Rewriting with unused statements should inline them") {
    val a = ir"val r = readDouble; val a = readInt; val b = r.toInt; b" rewrite {
      case ir"readDouble" => ir"val r = readInt; val a = r + 1; 20d"
    }
    assert(a =~= ir"val r = readInt; val a2 = r + 1; val a1 = readInt; val b = 20d.toInt; b")
  }
  
  test("Rewriting should not duplicate effects") {
    val a = ir"val r = readDouble; val b = r.toInt; val c = r.toDouble; b + c" rewrite {
      case ir"readDouble" => ir"val r = readInt; val a = r + 1; 20d"
    }
    assert(a =~= ir"val r = readInt; val a = r + 1; 20d.toInt + 20d.toDouble")
  }
  
  test("Rewriting a non-letbinding with a let-binding") {
    val a = ir"val a = 20.toDouble; a + 1" rewrite {
      case ir"20" => ir"readInt"
    }
    assert(a =~= ir"val r = readInt; val a = r.toDouble; a + 1")

    val b = ir"val a = 20.toDouble; a + 1" rewrite {
      case ir"20" => ir"val t = readInt; 40"
    }
    assert(b =~= ir"val t = readInt; val a = 40.toDouble; a + 1")
  }
  
  test("Rewriting should insert the generated code at the right position") {
    val a = ir"val f1 = (x: Int) => x + 1; val f2 = (x: Int) => x * 2; f1(f2(5))" rewrite {
      case ir"($f1: Int => Int)(($f2: Int => Int)(5))" => ir"($f1 compose $f2)(5)"
    }
    assert(a =~= ir"val f1 = (x: Int) => x + 1; val f2 = (x: Int) => x * 2; val f3 = f1 compose f2; f3(5)")

    val b = ir"List(1,2,3).map(_ * 2).map(_ * 4)" rewrite {
      case ir"($l: List[Int]).map($f1: Int => Int).map($f2: Int => Int)" => ir"$l.map($f2 compose $f1)"
    }
    assert(b =~= ir"val l = List(1, 2, 3); val f1 = (x: Int) => x * 2; val cbf1 = List.canBuildFrom; val f2 = (x: Int) => x * 4; val cbf2 = List.canBuildFrom; val f3 = f2 compose f1; l.map(f3)")
  }
  
  test("Squid paper") {
    
    // 3.4
    val a = ir"List(1,2,3).foldLeft(0)((acc,x) => acc+x) + 4" rewrite {
      case ir"($ls: List[Int]).foldLeft[Int]($init)($f)" =>
        ir"var cur = $init; $ls.foreach(x => cur = $f(cur, x)); cur"
    }
    assert(a =~=
      ir"val t = List(1, 2, 3); val f = ((acc: Int, x: Int) => acc+x); t.foldLeft(0)(f); var cur = 0; t.foreach(x => cur = f(cur, x)); cur + 4")
  }

  test("Rewriting simple expressions only once") {
    /*
     * TODO 
     * goes into an infinite loop since it rewrites 
     * at the "current" point. So the topdown transformer 
     * will apply the transformation again on what was rewritten.
     */
    //val a = ir"println((50, 60))" rewrite {
    //  case ir"($x:Int,$y:Int)" => ir"($y:Int,$x:Int)"
    //  //case ir"(${Const(n)}:Int)" => Const(n+1)
    //}
    //assert(a =~= ir"println((61,51))")
  }
  //
  //test("Function Rewritings") {
  //  val a = ir"(x: Int) => (x-5) * 32" rewrite {
  //    case ir"($b: Int) * 32" => ir"$b"
  //  }
  //  assert(a =~= ir"(x: Int) => x - 5")
  //
  //  val b = ir"(x: Int) => (x-5) * 32" rewrite {
  //    case ir"(x: Int) => ($b: Int) * 32" => dbg_ir"val x = 42; (p: Int) => $b + p"
  //  } alsoApply println
  //
  //  println(ir"val u = 42; (v: Int) => (u - 5) + v")
  //
  //  assert(b =~= ir"val u = 42; (v: Int) => (u - 5) + v")
  //}
}

object RewritingTests {
  object Embedding extends FastANF
  
  def f(x: => Double) = x
}
