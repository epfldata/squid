package squid
package anf

import ir._
import utils._
import squid.anf.analysis.BlockHelpers
import squid.anf.transfo.IdiomsNormalizer

object BlockExtrTests {

  object DSL extends SimpleANF with BlockHelpers with StandardEffects

}

/**
  * Created by lptk on 10/02/17.
  * 
  * TODO in RwR, xtor should also try to match the whole pgrm? -> cf Block xtor
  * 
  */
class BlockExtrTests extends MyFunSuite(BlockExtrTests.DSL) {
  import DSL.Predef._
  import DSL.Quasicodes._
  import base.{Block,WithResult,Closure}
  
  
  test("Basics") {
    
    val c = code"println(readInt); 42"
    
    c match {
      case Block(b) =>
        b.original eqt c
        b.res eqt code"42"
    }
    c match {
      case Block(WithResult(b,code"43")) => fail
      case Block(WithResult(b,code"42")) =>
    }
    
    def f(q:Code[_,{}]) = q rewrite {
      case code"while(${Block(b)}){}" => code"val c = ${b.original}; while(c){}"  // Stupid rewriting just to test the feature
    }
    code"while(readInt>0){}" |> f eqt code"val c = readInt>0; while(c){}"
    
  }
  
  
  test("Closure Extraction") {
    
    val f0 = code"(x:Int) => x+1"
    f0 match {
      case Closure(cls) =>
        cls.env eqt code"()"
        cls.fun eqt code"(_ : Unit) => $f0"
    }
    
    code"val r = readInt; (x:Int) => x+r" match {
      case Closure(cls) =>
        //println(cls)
        cls.env eqt code"readInt"
        cls.fun eqt code"(t: Int) => (x:Int) => x+t"
        
    }
    
    def f(q:Code[Option[Int => Int],{}]) = q rewrite {
      
      //case ir"($opt:Option[$ta]).flatMap($f)" => ???  // FIXME why no warning?!
      //case ir"($opt:Option[$ta]).map[$tb => $tc](x => ${Closure(cls)})" => // FIXME: current hygiene problem!! name 'x' is used in the `Closure` extractor and is confused!
      case code"($opt:Option[Int]).map[$tb => $tc](xyz => ${Closure(cls)})" =>
        
        assert(cls.env =~= code"Nil.size" || cls.env =~= code"(Nil.size, readDouble)")
        
        assert(cls.fun =~= code"(arg:Int) => (u: Int) => (xyz?:Int) + u + arg" || // Note: inserting `$xyz` instead of `(xyz?:Int)` does not work here
          cls.fun =~= code"(arg:(Int,Double)) => (u: Int) => (xyz?:Int) + u + (arg._1 * (arg._2 + arg._1)).toInt")
        
        import cls._
        
        code"""
          var envVar: $typE = squid.lib.nullValue[$typE]
          if ($opt.isEmpty) None else {
            val xyz = $opt.get;
            envVar = $env
            val r = $fun(envVar)
            Some(r) :  Option[$tb=>$tc]  // FIXME: why is this necessary? (otherwise, types the block to Some[Int=>Int], which breaks the comparison below)
          }
        """
        
    }
    
    val r0 = code"Option(42).map { n => val r = Nil.size; (m:Int) => n+m+r }" |> f
    r0 eqt ir{
      val x_0 = Option(42);
      var envVar_1: scala.Int = squid.lib.nullValue[scala.Int];
      if (x_0.isEmpty) scala.None
      else {
        val x_2 = scala.collection.immutable.Nil.size;
        envVar_1 = x_2;
        val x_3 = envVar_1;
        Some(((m_4: scala.Int) => x_0.get.+(m_4).+(x_3)))
      }
    }
    same(r0.run.get(-1), 41)
    
    val r1 = code"Option(42).map { n => val r = Nil.size; val s = readDouble+r; (m:Int) => n+m+(r*s).toInt }" |> f
    
    //println(r1.run.get(-1))  // not executing this because it contains a `readInt`
    
    r1 eqt ir[Option[Int=>Int]]{ // Note: type ascription necessary, otherwise it types the block with `Any`! FIXME shoudn't the code still be equivalent
      val x_0 = Option(42);
      var envVar_1 = squid.lib.nullValue[Int->Double];
      if (x_0.isEmpty) scala.None
      else {
        val x_2 = scala.collection.immutable.Nil.size;
        val s_ = readDouble
        envVar_1 = (x_2,s_);
        val x_3 = envVar_1;
        Some(((m_4: scala.Int) => x_0.get.+(m_4)+(x_3._1*(x_3._2 + x_3._1)).toInt))
      }
    }
    
  }
  
  
  
}
