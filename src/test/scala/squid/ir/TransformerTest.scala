package squid
package ir

class TransformerTest extends MyFunSuite/*(new SimpleAST)*/ {
  import DSL.Predef._
  
  object T extends SimpleRuleBasedTransformer with TopDownTransformer {
    val base: DSL.type = DSL
  }
  
  test ("Simple Rewritings") {
    T.rewrite {
      case code"666" => code"999"
      case code"42.toFloat" => code"42f" 
      case code"(${Const(n)}: Int).toDouble" => code"${Const(n.toDouble)}"
    }
    eqt(T.transform(code"666".rep), code"999".rep)
    eqt(T.transform(code"42.toFloat".rep), code"42f".rep)
    eqt(T.transform(code"22.toDouble".rep), code"22.0".rep)
    
    
    assertDoesNotCompile("""
      T.rewrite { case code"0.5" => code"42" }
    """) // Error:(25, 34) Cannot rewrite a term of type Double to a different type Int
    
    assertDoesNotCompile("""
      T.rewrite { case code"123" => code"($$n:Int)" }
    """) // Error:(26, 34) Cannot rewrite a term of context [Unknown Context] to an unrelated context Any{val n: Int}
    
  }
  
  test ("Rewritings With Subpatterns") {
    
    T.rewrite {
      case code"(${ code"($n: Int)+111" }: Int) * .5" => code"$n * .25"
    }
    eqt(T.transform(code"(readInt + 111) * .5".rep), code"readInt * .25".rep)
    
  }
  
  test ("No Additional Free Variables") {
    
    assertDoesNotCompile("""
      T.rewrite { case code"123" => code"($$n:Int)" }
    """) // Error:(26, 34) Cannot rewrite a term of context [Unknown Context] to an unrelated context Any{val n: Int}
    
  }
  
  test ("Function Rewritings") {
    
    assertDoesNotCompile("""
      T.rewrite { case code"(x: Int) => $b: Int" => b }
    """) // Error:(26, 50) Cannot rewrite a term of type Int => Int to a different type Int
    
    assertDoesNotCompile("""
      T.rewrite { case code"(x: Int) => $b: Int" => code"(y: Int) => $b" }
    """) // Error:(30, 50) Cannot rewrite a term of context [Unknown Context] to a stricter context [Unknown Context]{val x: Int}
    
    T.rewrite { case code"(x: Int) => ($b: Int) * 32" => code"val x = 42; (y: Int) => $b + y" }
    
    eqt(T.transform(code"(x: Int) => (x-5) * 32".rep), code"val u = 42; (v: Int) => (u - 5) + v".rep)
    
  }
  
  
  test ("Polymorphic Rewritings") {
    
    T.rewrite {
      case code"List[$t]($xs*).size" => code"${Const(xs.size)}"
      case code"($ls: List[$t0]).map($f: t0 => $t1).map($g: t1 => $t2)" =>
        code"$ls.map($f andThen $g)"
    }
    
    eqt(T.transform(code"List(1,2,3).size".rep), code"3".rep)
    eqt(T.transform(code"List(1,2,3) map (_ + 1) map (_.toDouble)".rep),
                    code"List(1,2,3) map { ((_:Int) + 1) andThen ((_:Int).toDouble) }".rep)
    
  }
  
  
  test ("With Top-Level Pattern Alias") {
    
    var saved = Option.empty[Code[Any,_]]
    
    T.rewrite {
      
      // Note that we cannot get a precise type for `x` here,
      // because the patmat has to be typed before it goes through the `rewrite` macro
      case x @ code"Option[Int]($v).get" =>
        saved = Some(x)
        code"$v"
      
    }
    
    code"println(Option(42).get)" transformWith T eqt code"println(42)"
    
    saved.get eqt code"Option(42).get"
    
  }
  
  
  
}

