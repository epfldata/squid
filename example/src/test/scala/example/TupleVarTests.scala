package example

import org.scalatest.FunSuite
import squid.MyFunSuite
import squid.ir._
import squid.lang.InspectableBase
import squid.utils._

object Code extends squid.ir.SimpleANF with squid.lang.ScalaCore with squid.anf.analysis.BlockHelpers
import Code.Predef._
import Code.{SelfTransformer=>CST}

object DeTup extends CST with TupleVarOptim with TopDownTransformer
object Norm extends CST with VarNormalizer with squid.anf.transfo.LogicNormalizer with TopDownTransformer
object DeTupFix extends Code.TransformerWrapper(DeTup) with FixPointTransformer
object DeTupNormFix extends Code.TransformerWrapper(DeTup,Norm) with FixPointTransformer

/**
  * Created by lptk on 01/02/17.
  */
class TupleVarTests extends MyFunSuite(Code) {
  
  test("Recursive Detupling") {
    
    val c0 = code"""
      var a = (1,(2,()))
      println(a._1, a._2._1, a._2._2)
    """
    
    c0 transformWith DeTupFix eqt code"""
      var a = 1
      var b = 2
      var c = ()
      println(a,b,c)
    """
    
  }
  
  test("Recursive Detupling with nulls and units") {
    
    val c0 = code"""
      var a: (Int,(String,Unit)) = null
      a = (1,("ok",()))
      println(a._1, a._2._1, a._2._2)
    """
    
    c0 transformWith DeTupNormFix eqt code"""
      var isNull_0: Bool = true
      var a_1: Int = 0
      var isNull_2: Bool = true
      var a_3: String = null
      a_1 = 1
      a_3 = "ok"
      isNull_2 = false
      isNull_0 = false
      val x_4 = isNull_0
      val x_5 = !x_4
      Predef.assert(x_5)
      val x_6 = a_1
      val x_7 = isNull_0
      val x_8 = !x_7
      Predef.assert(x_8)
      val x_9 = isNull_2
      val x_10 = !x_9
      Predef.assert(x_10)
      val x_11 = a_3
      val x_12 = isNull_0
      val x_13 = !x_12
      Predef.assert(x_13)
      val x_14 = isNull_2
      val x_15 = !x_14
      Predef.assert(x_15)
      val x_16 = Tuple3.apply[Int, String, Unit](x_6, x_11, ())
      println(x_16)
    """
    
  }
    
    //// TODO normalize to this!
    //c0 transformWith DeTupNormFix eqt ir"""
    //  var a = 1
    //  var b = "ok"
    //  println(a,b,())
    //"""
  
  test("Removal of Var[Unit]") {
    
    val c0 = code"var vu = (); println(vu); vu = (); vu"
    c0 transformWith DeTupNormFix eqt code"println(()); ()"
    
  }
  
  
  
}
