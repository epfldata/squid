package example

/**
  * Created by lptk on 02/12/16.
  * 
  * Note: cannot use `var acc = ir"1.0" : IR[Double, x.Ctx]` on the rhs of the rewriting,
  * because we would get {{{ _ <: Ctx }}}, which is not sufficient
  * (see the definition of `Ctx`, since it mirrors a contravariant type parameter).
  * 
  */
object PowOptim extends App {
  
  object Code extends squid.ir.SimpleAST
  import Code.Predef._
  import Code.Quasicodes._
  
  def opt[T,C](pgrm: Code[T,C]) = pgrm rewrite {
    case code"Math.pow($x, ${Const(d)})"
    if d.isValidInt && (0 to 16 contains d.toInt) =>
      var acc = code"1.0" withContextOf x
      for (n <- 1 to d.toInt) acc = code"$acc * $x"
      acc
  }
  
  import Math._
  val normCode = opt(ir{ (x:Double,y:Double) => sqrt(pow(x,2) + pow(y,2)) })
  println(normCode)
  
  //val norm = normCode.compile  // TODO port from SCP
  val norm = normCode.run
  println(norm)
  
  println(norm(1,2))
  
}
