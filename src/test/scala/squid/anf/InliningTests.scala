package squid
package anf

import utils._
import ir._

/**
  * Created by lptk on 30/01/17.
  */
class InliningTests extends MyFunSuite(SimpleANFTests.DSL) {
  import DSL.Predef._
  
  object AppNorm extends DSL.SelfTransformer
      with CurryEncoding.ApplicationNormalizer
      with TopDownTransformer
      with FixPointRuleBasedTransformer
    
  
  val one = Const(1)
  
  test("Curry-Normalized Functions") { // would also be interesting to test it online
    
    code"((x: Int) => x+1)(42)" eqt code"42 + $one" // Code insertion to avoid the Scala typer from reducing the expr...
    
    val x = code"((x: Int,y:Int) => x+y)(12,34)"
    assert(x.rep.asBlock._1.isEmpty)
    x transformWith AppNorm eqt code"12 + ${Const(34)}"
    
  }
  
  test("Messing with Bindings") {
    
    code"val f = (x: Int) => x+1; f(0)+f(1)" eqt code"(0+$one)+(1+$one)" // no prob here; why?
    
    code"val f = (x: Int) => {val y = readInt; x+y}; f(0)+f(1)" eqt code"(0+readInt)+(1+readInt)"
    
    code"val f = (x: Int) => {val y = readInt; x+y}; f(f(0))" eqt 
      code"val a = readInt; val b = 0+a; val c = readInt; b+c"
    
    val fun = code"(x: (Int => Int)) => x(readInt)"
    val c0 = code"val f = $fun; f(a => f(b => a*b))"
    val c1 = code"val f = $fun; val g = (x: (Int => Int)) => x(readInt); f(a => g(b => a*b))"
    val c2 = code"readInt*readInt"
    c0 eqt c1
    c1 eqt c2
    c2 eqt c0
    
    code"val f = (x: (Int => Int)) => {val y = x(readInt); y+1}; f(a => f(b => a*b))" eqt
      code"readInt*readInt+1+1"
    
  }
  
  test("Manually Messing with Bindings") {
    import base._
    
    val a = bindVal("a",typeRepOf[Int],Nil)
    val b = bindVal("b",typeRepOf[Int],Nil)
    val f = abs(a,rep(a))
    val g = abs(b,rep(a))
    
    eqt(inline(a, f, a|>rep), f) // not transformed because `f`'s parameter is rebound, seeing that the original is contained in the inlined argument
    eqtBy(inline(a, g, b|>rep), f, false)(_ =~= _) // rebinds g's param so we don't end up capturing the inlined argument, making the identity (f)
    eqt(inline(b, g, b|>rep), g) // rebinds g's param so we don't end up capturing the inlined argument, making the identity (f)
    
    eqt(inline(a, f, const(0)), code"(a:Int)=>0".rep)
    
    val x = code"identity(${Code[Int=>Int,{}](f)})(${Code[Int,{}](b|>rep)})"
    eqt(inline(b, x.rep, const(0)), code"identity((x:Int)=>x)(0)".rep)
    
    intercept[IllegalArgumentException](inline(a, f, f)) // cannot inline an argument that binds the variable for which it is inlined
    
  }
  
}
