package squid
package functional

import squid.ir.{BindingNormalizer, TopDownTransformer}
import utils._

class FoldTupleVarOptims extends MyFunSuite(NormDSL) {
  import DSL.Predef._
  
  object Optim extends FoldTupleVarOptim.ForNormDSL
  
  test("Foldleft to foreach to while") {
    
    val ls = code"$$ls: List[Int]"
    val f = code"$$f: ((Int, Int) => Int)"
    
    code"$ls.foldLeft(0)($f)" transformWith Optim eqt
    code"""
      var acc = 0;
      {
        var ite = $ls
        while (ite nonEmpty) {
          { val tmp = ite.head; acc = $f(acc,tmp) }
          ite = ite.tail
        }
      }
      acc
    """
    
  }
  
  test("Tuple Variable Inlining") {
    
    eqtBy(code"var two = (1,0); while (two._1 + two._2 < 42) two = (two._1 + 1, two._2 + 2); two" transformWith Optim,
    code"""
      var a = 1;
      var b = 0;
      while (a + b < 42) {
        a += 1
        b += 2
      }
      (a, b)
    """)(_ =~= _)
    
  }
  
  test("FoldLeft on tuple to while on scalar vars") {
    
    // TODO make the combined optims work!
    // Problem is: `cur` is not assigned a tuple, but an applied Function2 which is equivalent to a tuple, and we don't inline it...
    // Even without inlining, we could solve the problem by just normalizing. Eg put it in ANF.
    
    //println(ir"List(1,2,3).foldLeft((0,0))((acc,x) => (acc._2, acc._1+x))" transformWith Optim)
    //println(ir"val r = List(1,2,3).foldLeft((0,0))((acc,x) => (acc._2, acc._1+x)); r._1 + r._2" transformWith Optim)
    
  }
  
  
  object Stopt extends StaticOptimizer[FoldTupleVarOptim.ForNormDSL]
  import Stopt._
  
  test("Static optimization") {
    
    
    assert(optimize {
      List(1,2,3).foldLeft(0)(_ + _)
    } == 6)
    
    
    assert(optimize {
      //List(1,2,3).foldLeft(0)(acc_n => acc_n._1 + acc_n._2)
      //List(1,2,3).foldLeft((0,0))((acc,x) => (acc._2,acc._1+x))
      val r = List(1,2,3).foldLeft((0,0))((acc,x) => (acc._2,acc._1+x)); r._1 + r._2
    } == (2+4))
    
    
  }
  
}
