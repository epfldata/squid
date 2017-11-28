package squid.scback

import collection.mutable.ArrayBuffer
import ch.epfl.data.sc.pardis
import pardis.ir.Constant

class SimpleRewritingTests extends PardisTestSuite {
  
  import Sqd.Predef._
  import Sqd.Quasicodes._
  
  
  test("Constants") {
    
    sameDefs(code"666" rewrite {
      case code"666" => code"42"
    }, code"42")
    
    sameDefs(code"666" rewrite {
      case code"666" => code"42.0.toInt"
    }, code"42.0.toInt")
    
    sameDefs(code"666.0.toInt" rewrite {
      case code"666.0" => code"42.0"
    }, code"42.0.toInt")
    
  }
  
  
  test("FunctionN") {
    
    sameDefs(code"() => println(666)" rewrite {
      case code"666" => code"42"
    }, code"() => println(42)")
    
    sameDefs(code"val f = () => println(666); f()" rewrite {
      case code"666" => code"42"
    }, code"val f = () => println(42); f()")
    
    sameDefs(code"ArrayBuffer(1,2,3) map ((x: Int) => println(666))" rewrite {
      case code"666" => code"42"
    }, code"ArrayBuffer(1,2,3) map ((x: Int) => println(42))")
    
    sameDefs(code"(a:Int,b:Double,c:String) => ((a,b),Option[String](null))" rewrite {
      case code"(($x:Int,$y:Double),Option[String](null))" => code"val t = ($y.toInt, $x.toDouble); (t, Option(${Const("ok")}))"
    }, code"""(a:Int,b:Double,c:String) => { ((b.toInt, a.toDouble), Option("ok")) }""")
    
  }
  

}