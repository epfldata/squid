package squid
package feature

import utils.Debug._

class Genericity extends MyFunSuite {
  import TestDSL.Predef._
  
  
  test("Generic Contexts and AnyRef") {
    
    assertCompiles(""" def constructTuple[C](x: Code[Int, C]): Code[Int, C] = code"$x + ${Const(123)}" """)
    assertCompiles(""" def constructTuple[C]: Code[Int, C] = code"${Const(123):Code[Int,AnyRef]}" """)
    
  }
  
  
  test("List") {
    
    val ls = code"List(1.0, 2.0)"
    //println(ls.rep.typ)
    
    
    //def foo[A: TypeEv](x: Q[A,{}]) = x match {
    def foo[A: TypeEv](x: Q[List[A],{}]) = x match {
      case code"List[A]($x,$y)" =>
        //println(typeEv[A])
        code"List($y,$x)"
    }
    
    //println(foo(ls))
    
    (ls: Q[_,{}]) match {
      case code"$ls: List[Int]" => ???
      case code"$ls: List[Double]" =>
    }
    
    
    (ls: Q[_,{}]) match {
      case code"$ls: List[$t]" => eqt(t, codeTypeOf[Double])
    }
    
    /*
    // Note: Scala weirdness:
    { trait t
      import scala.reflect.runtime.universe._
      implicit val _t_0: TypeTag[t] = ???
      typeTag[t]
      typeTag[List[t]]
    }
    */
    
    
    
  }
  
}



