package squid.scback

import collection.mutable.ArrayBuffer
import ch.epfl.data.sc.pardis.ir.Constant

class PardisIRFeatureTests extends PardisTestSuite {
  
  import Sqd.Predef._
  import Sqd.Quasicodes._
  import Sqd.{block, pardisBlock}
  
  
  
  test("If Then Else") {
    val q = pardisBlock(ir{ if (1.5.toInt > 0) println("ok") else "ko" })
    assert(q.stmts.size == 3)
  }
  
  
  //test("While Loop") {} // TODO
  

  test("Lambdas & Applications") {
    
    def f = ir{ (a: Int) => a+1 }
    
    val q0 = block(f)
    val q1 = block(ir{ $(f)(42) })
    
    //println(q0)
    //println(q1)
    
  }
  
  
  test("Methods") {
    
    //val q = block(ir{ println(new ArrayBuffer[Int](0) append 1) })
    val q = ir{ println(new ArrayBuffer[Int](0) append 1) }
    //println(q)
    
  }
  
  
  test("Constructors") {
    
    val q = block(ir{ new ArrayBuffer(42) })
    
    q.rep match {
      //case SDSL.TopLevelBlock(b) =>
      case b: Sqd.Block =>
        assert(b.stmts.size == 1)
        b.res.correspondingNode match {
          case SC.ArrayBufferNew1(Constant(42)) =>
        }
    }
  }
  
  
  test("Companion Object Methods") {
    // Note: both `apply` methods mirrored in MirrorSeq and MirrorArrayBuffer refer to the _same_ method defined in GenericCompanion
    // so one will overwrite the other; to avoid that we'll have to manually make the binding by overriding `methodApp`
    
    val q0 = block(ir{ Seq(1,2,3) })         // ir"{ val x23 = ArrayBuffer.apply(1, 2, 3) x23 }"
    val q1 = block(ir{ ArrayBuffer(1,2,3) }) // ir"{ val x23 = ArrayBuffer.apply(1, 2, 3) x23 }"
    
    //println(q0)
    //println(q1)
    
    // Note: the first statement is a `PardisLiftedSeq`
    assert(stmts(q0).tail.head.rhs.isInstanceOf[SC.SeqApplyObject[_]])
    assert(stmts(q1).tail.head.rhs.isInstanceOf[SC.ArrayBufferApplyObject[_]])
    
  }
  
  
  test("String") {
    
    val q = block(ir{ println(((x: String) => x.length)("ok")) })
    //println(q)
    
  }
  
  
  test("Type Ascription") { // TODO
    println(code"42:Any")
  }
  
  
  //test("Variables") {}  // TODO
  
  
  
}
