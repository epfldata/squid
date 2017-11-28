package stagerwr

import squid.utils._

//import Embedding.Predef._
import Embedding.Predef.{Code=>IR,_}
//import Embedding.SimplePredef._
import Embedding.SimplePredef.{Rep => Code, _}
import Embedding.Quasicodes._

/**
  * Created by lptk on 16/06/17.
  */
object PowerTests extends App {
  //type Code[T] = Rep[T]
  
  //import Embedding.Predef._
  //import Embedding.SimplePredef.{Rep => Code}
  implicit class CodeOps[T](private val r: Code[T]) extends AnyVal {
    def capture[C] = r: IR[T,C]
  }
  
  
  def power(exp: Int, base: Code[Double]): Code[Double] =
    if (exp == 0) code"1.0"
    else if (exp % 2 == 0) code"""
      val tmp = ${power(exp/2, base)}
      tmp * tmp
    """
    else code"$base * ${power(exp-1, base)}"
  
  def powerCurried(exp: Int)(base: Code[Double]): Code[Double] = power(exp, base)
  def powerCurried2(exp: Int): Code[Double] => Code[Double] = power(exp, _)
  //def powerCurried2(exp: Int): IR[Double,_] => IR[Double,_] = power(exp, _).asClosedIR
  
  power(3,code"42.0") alsoApply println
  
  //val pow3 = ir"(x:Double) => ${power(3, ir"x")}"  // doesn't type check, as expected
  //val pow3 = ir"(x:Double) => ${power(3, ir"x?:Double")}"  // doesn't capture, as expected
  //val pow3 = ir"(x:Double) => ${power(3, ir"x?:Double"):IR[Double,{val x:Double}]}" // captures, but ulgy
  //val pow3 = ir"(x:Double) => ${power(3, ir"x?:Double").capture[{val x:Double}]}" // captures, still ugly
  //val pow3 = ir"(x:Double) => ${powerCurried(3) _}(x)" // trailing underscore kind of awkward
  val pow3 = code"(x:Double) => ${powerCurried2(3)}(x)" // TODOne make it work
  
  pow3 alsoApply println
  pow3.run.apply(.5) alsoApply println
  
  
  // TODO:
  /*
  val f = (x:Code[Int],y:Code[Int]) => ir"$x + $y"
  ir"${f}(1,2)" alsoApply println
  */
    
}

// TODO test Code and IR fun-lifting

