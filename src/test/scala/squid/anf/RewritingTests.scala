package squid
package anf

import ir._

/**
  * Created by lptk on 02/02/17.
  * 
  * TODO port some of the seq matching tests from scBackend
  * 
  */
class RewritingTests extends MyFunSuite(SimpleANFTests.DSL) {
  import DSL.Predef._
  
  test("Rewriting simple expressions only once") {
    
    val a = code"println((50,60))"
    val b = a rewrite {
      case code"($x:Int,$y:Int)" =>
        code"($y:Int,$x:Int)"
      case code"(${Const(n)}:Int)" => Const(n+1)
    }
    b eqt code"println((61,51))"
    
  }
  
  test("Rewriting Sequences of Bindings") {
    
    val a = code"val aaa = readInt; val bbb = readDouble.toInt; aaa+bbb"  // FIXMElater: why isn't name 'bbb' conserved?
    val b = a rewrite {
      case code"readDouble.toInt" =>
        code"readInt"
    }
    b eqt code"val aa = readInt; val bb = readInt; aa+bb"
    
    {
      val a = code"val a = 11.toDouble; val b = 22.toDouble; val c = 33.toDouble; (a,b,c)"
      val c = a rewrite {
        case code"val a = ($x:Int).toDouble; val b = ($y:Int).toDouble; $body: $bt" =>
          code"val a = ($x+$y).toDouble/2; val b = a; $body"
      }
      c eqt code"val a = (11+${code"22"}).toDouble/2; val c = 33.toDouble; (a,a,c)"
      
      /*
      // TODO make this work like the one above
      val d = a rewrite {
        case ir"val a = ($x:Int).toDouble; ($y:Int).toDouble" =>
          ir"($x+$y).toDouble/2"
      }
      println(d)
      //d eqt ir"val a = (11+${ir"22"}).toDouble/2; val c = 33.toDouble; (a,a,c)"
      */
    }
    
    
  }
  
  test("Rewriting Sequences of Effects") {
    
    val c0 = code"print(1); print(2); print(3); print(4)"
    
    c0 rewrite {
      case code"print(1); print(2)" => code"print(12)"
    } eqt code"print(12); print(3); print(4)"
    
    c0 rewrite {
      case code"print(2); print(3)" => code"print(23)"
    } eqt code"print(1); print(23); print(4)"
    
    c0 rewrite {
      case code"print(3); print(4)" => code"print(34)"
    } eqt code"print(1); print(2); print(34)"
    
  }
  
  test("Rewriting Trivial Arguments") {
    
    val a = code"val a = 0.toDouble; val b = 0.toDouble; val c = 0.toDouble; (a,b,c)"
    val b = a rewrite {
      case code"(${Const(n)}:Int).toDouble" => code"${Const(n+1)}.toDouble"
    }
    b eqt code"val a = 1.toDouble; val b = 1.toDouble; val c = 1.toDouble; (a,b,c)"
    
  }
  
  test("Rewriting named effects") {
    
    def f(x: Code[_,{}]) = x rewrite { case code"readInt; readInt" => code"42" }
    code"val n = readInt; val m = readInt; println" |> f eqt code"println"
    code"val n = readInt; val m = readInt; println(m)" |> f eqt code"println(42)"
    code"val n = readInt; val m = readInt; println(m+n)" |> (a => a |> f eqt a)
    
    // Should also work with early return!
    def g(x: Code[_,{}]) = x rewrite { case code"readInt; readInt" => Return(code"readInt; readInt+1") }
    code"val n = readInt; val m = readInt; print(n+m)" |> (a => a |> g eqt a)
    code"val n = readInt; val m = readInt; print(n+m); readInt; readInt" |> g eqt
      code"val n = readInt; val m = readInt; print(n+m); readInt; readInt+1"
    
  }
  
  test("Named rewriting of effects") {
    
    def f(x: Code[_,{}]) = x rewrite { case code"val n = readInt; $body: $bt" => code"val n = ???; $body" }
    code"println; readInt; println" |> f eqt code"println; val lol = ???; println"
    //ir"println; readInt; println" |> f eqt ir"println; ???; println" // TODO allow this; make repEq use toBlock...?
    
    def g(x: Code[_,{val n:Int;val m:Int}]) = x rewrite { case code"val n = readInt; n+1" => code"readDouble.toInt" }
    code"println(readInt+1)" |> g eqt code"println(readDouble.toInt)"
    code"val n = readInt; println(n+1)" |> g eqt code"println(readDouble.toInt)"
    code"readInt; (m?:Int)+1" |> (a => a |> g eqt a)
    code"readInt; (n?:Int)+1" |> (a => a |> g eqt a)
    code"val x = readInt; (n?:Int)+1" |> (a => a |> g eqt a)
    
  }
  
  test("Soundly Swallowing Bindings or Not") {
    
    def f(x: Code[_,{}]) = x rewrite { case code"readInt; $body: $bt" => body }
    code"readInt;1" |> f eqt code"1"
    code"readInt+1" |> (a => a |> f eqt a)
    
    def fe(x: Code[_,{}]) = x rewrite { case code"readInt; $body: $bt" => Return(body) }
    code"readInt;1" |> fe eqt code"1"
    code"readInt+1" |> (a => a |> fe eqt a)
    
    def g(x: Code[_,{}]) = x rewrite { case code"readInt; println($x)" => code"print($x)" }
    code"val ri = readInt; println(ri); ri+1" |> (a => a |> g eqt a)
    code"val ri = readInt; println(ri); 42" |> (a => a |> g eqt a)
    code"val ri = readInt; println(123); 42" |> g eqt code"print(123); 42"
    code"val ri = readInt; println(123)" |> g eqt code"print(123)"
    code"val ri = readInt; println(ri)" |> (a => a |> g eqt a)
    code"readInt; println(0)" |> g eqt code"print(0)"
    code"readInt; println(0); 1" |> g eqt code"print(0); 1"
    
    def ge(x: Code[_,{}]) = x rewrite { case code"readInt; println($x)" => Return(code"print($x)") }
    code"val ri = readInt; println(ri); ri+1" |> (a => a |> ge eqt a)
    code"val ri = readInt; println(ri); 42" |> (a => a |> ge eqt a)
    code"val ri = readInt; println(123); 42" |> ge eqt code"print(123); 42"
    code"val ri = readInt; println(123)" |> ge eqt code"print(123)"
    code"val ri = readInt; println(ri)" |> (a => a |> ge eqt a)
    code"readInt; println(0)" |> ge eqt code"print(0)"
    code"readInt; println(0); 1" |> ge eqt code"print(0); 1"
    
  }
  
  
}
