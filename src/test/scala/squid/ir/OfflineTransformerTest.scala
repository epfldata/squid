package squid
package ir

import squid.lang.InspectableBase

class OfflineTransformerTest extends MyFunSuite {
  import TestDSL.Predef._
  
  test ("Basic Rewriting") {
    
    object Trans extends TestDSL.SelfTransformer with SimpleRuleBasedTransformer with BottomUpTransformer {
      rewrite { case code"666" => code"42" }
    }
    eqt( code"('answer, 666)" transformWith Trans, code"('answer, 42)" )
    
  }
  
  test ("Prevent Widened Base Type") {
    
    //assertDoesNotCompile("""
      object Trans extends SimpleRuleBasedTransformer with BottomUpTransformer {
        val base: InspectableBase = TestDSL
        //rewrite { case ir"42" => ir"42" }  // lol, scalac stack overflow...
      }
    //""") //Used to get: // Error:(10, 24) Embedding Error: Could not verify that `scp.ir.OfflineTransformerTest.Trans.base.type` is the same as `OfflineTransformerTest.this.DSL.type`
    
  }
  
  test ("Bottom Up Rewriting") {
    
    object Trans extends TestDSL.SelfTransformer with SimpleRuleBasedTransformer with BottomUpTransformer { rewrite {
      case code"(1,0)" => code"(0,1)"
      case code"(0,(0,1))" => code"(1,(0,0))"
      case code"(0,(1,0))" => code"(1,(1,1))"
    }}
    eqt( code"(0,(1,0))" transformWith Trans, code"(1,(0,0))" )
    
  }
  
  
}
