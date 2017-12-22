// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package squid
package functional

import squid.ir.{BindingNormalizer, TopDownTransformer}
import utils._

class FoldTupleVarOptimsNew extends MyFunSuite(NormDSL) {
  import DSL.Predef._
  
  object Optim extends FoldTupleVarOptimNew.ForNormDSL
  
  test("Foldleft to foreach to while") {
    
    val ls = code"?ls: List[Int]"
    val f = code"?f: ((Int, Int) => Int)"
    
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
  
  
  object Stopt extends StaticOptimizer[FoldTupleVarOptimNew.ForNormDSL]
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
