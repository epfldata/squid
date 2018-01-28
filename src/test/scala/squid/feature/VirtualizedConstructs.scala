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
package feature

class VirtualizedConstructs extends MyFunSuite {
  import TestDSL.Predef._
  
  test("If-Then-Else") {
    
    val ite = code"if (1 > 2) 666 else 42"
    
    ite match {
      case code"if ($c) $t else $e" => // scrutinee type Int is propagated to the branch holes 
    }
    
    ite matches { // scrutinee type erased by `matches`
      
      //case ir"if ($c) $t else $e" => fail // infers Nothing for the return type... generates a warning
      //case ir"if ($c) $t: Nothing else $e: Nothing" => fail // still generates an annoying warning (because it's desugared to IfThenElse[Nothing](...)) ... so I commented
      
      //case ir"scp.lib.IfThenElse[Nothing]($c, $t, $e)" => fail // Warning:(14, 12) Type inferred for hole 't' was Nothing. Ascribe the hole explicitly to remove this warning.
      case code"squid.lib.IfThenElse[Nothing]($c, $t:Nothing, $e:Nothing)" => fail
        
      case code"if ($c) $t else $e: Int" =>
        c eqt code"1 > 2"
        t eqt code"666"
        e eqt code"42"
    } and {
      case code"if ($c) $t else $e: $tp" => eqt(tp.rep, typeRepOf[Int])
    }
    
    assert(ite.run == 42)
    
  }
  
  test("While") {
    
    code"while (readInt > 0) println('ok)" match {
      case code"while ($cond) $loop" =>
        cond eqt code"readInt > 0"
        loop eqt code"println('ok)"
    }
    
    import lib.While
    eqt(code"while(true) ()",
        code"While(true, ())")
    eqt(code"while(true) readInt",
        code"While(true, readInt)")
    eqt(code"(while(true) readInt): Unit",
        code"While(true,  readInt): Unit")
    eqt(code"(while(true) (readInt: Unit)): Unit",
        code"While(true,   readInt: Unit):  Unit")
    
    code"while (true) readInt" match {
      case code"while (true) $x" =>
        x eqt code"readInt; ()"
        x eqt code"readInt: Unit"
    }
    
  }
  
  test("Imperative") {
    import VirtualizedConstructs._
    
    setEv(0)
    
    val impure = code"setEv(getEv+1); setEv(getEv+1); getEv"
    
    impure match {
      case code"setEv(getEv+(${Const(n)}:Int)); setEv(getEv+1); getEv" => assert(n == 1)
    }
    impure matches {
    // Oddity: with 'matches', the 'ConstQ' extraction fails with: Error:(48, 31) No TypeTag available for A
    //case ir"setEv(getEv+(${ConstQ(n:Int)}:Int)); getEv" => assert(n == 1) // fixme ?!
      case code"setEv(getEv+1); setEv(getEv+1); getEv" =>
    } and {
      case code"lib.Imperative(setEv(getEv+1), setEv(getEv+1))(getEv)" =>
    }
    
    same(impure.run, 2)
    same(getEv, 2)
    
    same(code"ev = 0; ev".run, 0)
    same(getEv, 0)
    
    
    // Support for translation done by Scala:  nonUnitValue ~> { nonUnitValue; () }
    code"getEv; getEv; getEv" matches {
      case code"lib.Imperative(getEv,getEv)(getEv)" =>
    }
    
    // Just checking virtualization also works here:
    eqt( code"val x = {println; 42}; x",  code"val x = lib.Imperative(println)(42); x" )
    
    val q = code"readInt; readInt"
    q match { case code"$eff; readInt" => eff eqt code"readInt" }
    
    code"{ val x = 0; println }; 0" eqt code"${ code"val x = 0; println" }; 0"
    
  }
  
  test("Variables") {
    
    eqt( code"var x = 0; x = 1; x",  code"val x = lib.MutVar(0); x := 1; x!" )

    eqt( code"var x = 0; x += 1",  code"val x = lib.MutVar(0); x := x.! + 1" )
    
    same(code"val lol = 42; var v = lol-1; v += 1; v.toDouble".run, 42.0)
    
  }
  
}
object VirtualizedConstructs {
  var ev = 0
  def setEv(value: Int) = ev = value
  def getEv = ev
}










