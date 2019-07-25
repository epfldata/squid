package squid.haskellopt

import squid.utils._
import org.scalatest.FunSuite

class OptTests extends FunSuite {
  object TestHarness extends TestHarness
  
  test("Lists") {
    //pipeline("haskellopt/target/dump/Lists.pass-0000.cbor")
    //pipeline("haskellopt/target/dump/Lists.pass-0001.cbor")
    //for (i <- 2 to 9) pipeline(s"haskellopt/target/dump/Lists.pass-000$i.cbor")
    TestHarness("Lists")
    // FIXMEnot does not reduce at all!
    // FIXMEnot generates extra params!
  }
  test("Basics") {
    TestHarness("Basics")
    //TestHarness("Basics", exec = true)
    //TestHarness("Basics", "0000"::Nil)
  }
  test("PatMat") {
    // -- TODO optimize across case branches
    TestHarness("PatMat")
    //TestHarness("PatMat", "0000"::Nil)
  }
  test("PatMatRec") {
    //TestHarness("PatMatRec")
    TestHarness("PatMatRec", "0000"::Nil)
    //TestHarness("PatMatRec", "0001"::Nil) // FIXME apparently-infinite loop, printing "MAX PATH SIZE REACHED!"
  }
  test("PatMatRec2") {
    TestHarness("PatMatRec2")
    /*
    FIXME: the `usum` example here demonstrates a current problem: with all three examples together, we end up rewriting
           lots of things (more than 600 rewrite iterations with `MaxPathSize = 32`), but it's mostly in dead branches!
    */
  }
  test("Motiv") {
    TestHarness("Motiv")
  }
  test("MotivLocal") {
    TestHarness("MotivLocal")
  }
  test("ListFusion") {
    // FIXME this test generates code nondeterministically (order of two definitions keeps changing...)
    //TestHarness("ListFusion")
    TestHarness("ListFusionPaper")
    //TestHarness("ListFusion", "0000"::Nil)
    //TestHarness("ListFusion", (for (i <- 2 to 9) yield s"000$i").toList, opt = true)
  }
  test("ListFusionBTest") {
    TestHarness("ListFusionBench")
  }
  test("SimpleRec") {
    TestHarness("SimpleRec")
  }
  test("HigherOrder") {
    TestHarness("HigherOrder")
    //TestHarness("HigherOrder", "0000"::Nil)
  }
  test("HigherOrderHard") {
    //TestHarness("HigherOrderHard") // FIXME scope extrusion
    TestHarness("HigherOrderHard", compileResult = false)
    //TestHarness("HigherOrderHard", "0000"::Nil)
    //TestHarness("HigherOrderHard", "0001"::Nil)
  }
  test("HigherOrderRec") {
    TestHarness("HigherOrderRec", exec = true)
    //TestHarness("HigherOrderRec", compileResult = false)
    //TestHarness("HigherOrderRec")
    //TestHarness("HigherOrderRec", "0000"::Nil)
    //TestHarness("HigherOrderRec", "0001"::Nil)
  }
  test("HigherOrderRec2") { // FIXME-later: the minimized lack of reduction problem: due to passing f through each recursive call...
    TestHarness("HigherOrderRec2", dumpGraph = true)
    //TestHarness("HigherOrderRec2", dumpGraph = true, compileResult = false)
    //TestHarness("HigherOrderRec2", "0000"::Nil, dumpGraph = true)
  }
  test("HigherOrderRec3") {
    // FIXME-later: not fully reduced?: see k app -- probably same reason as HigherOrderRec2
    TestHarness("HigherOrderRec3")
    
    //TestHarness("HigherOrderRec3", "0000"::Nil)
    //TestHarness("HigherOrderRec3", "0001"::Nil)
  }
  test("HigherOrderRec4") {
    TestHarness("HigherOrderRec4", dumpGraph = true)
    //TestHarness("HigherOrderRec4", "0000"::Nil, dumpGraph = true)
  }
  test("HigherOrderRec5") {
    // Note: it looks like the thing is not fully reduced (see k app), but I think it happens on an impossible branch...
    TestHarness("HigherOrderRec5")
  }
  test("HigherOrderRecLocal") {
    TestHarness("HigherOrderRecLocal")
  }
  test("BuildFoldr") {
    TestHarness("BuildFoldr", dumpGraph = true)
    //TestHarness("BuildFoldr", dumpGraph = true, compileResult = false)
  }
  test("IterCont") { // used to have dumpGraph = true, but now that I added code in this test, the graph has become pretty big
    TestHarness("IterCont", exec = true)
    //TestHarness("IterCont", "0000"::Nil, compileResult = false, exec = true)
    //TestHarness("IterCont", "0001"::Nil, exec = true)
  }
  test("IterContNonlinear") {
    // FIXME commented count impl
    //TestHarness("IterContNonlinear", exec = true)
    TestHarness("IterContNonlinear", "0000"::Nil, exec = true)
    //TestHarness("IterContNonlinear", "0001"::Nil, exec = true) // FIXME loops in rewriting
  }
  test("IterCont2") {
    // Note: used to yield incorrect result [0,0,0] when we used the erroneous recursive call/arg kludge in the old scheduler
    // FIXME-later: not fully reduced: nats still constructs k/s lambdas, because of the threading of `f` hrough recursive calls...
    TestHarness("IterCont2", exec = true)
    //TestHarness("IterCont2", "0000"::Nil, exec = true) // Note: for pass 0001, the old scheduler generates a program that never terminates...
    //TestHarness("IterCont2", "0000"::Nil, exec = true, compileResult = false)
    //TestHarness("IterCont2", "0000"::Nil, exec = true)
    //TestHarness("IterCont2", "0000"::Nil)
    //TestHarness("IterCont2", "0001"::Nil)
    //TestHarness("IterCont2", "0001"::Nil, opt = true)
  }
  test("IterContLocal") {
    TestHarness("IterContLocal", exec = true)
    //TestHarness("IterContLocal", "0000"::Nil/*, exec = true*/)
    //TestHarness("IterContLocal", exec = true)
    //TestHarness("IterContLocal", "0001"::Nil, exec = true) // works now!
  }
  test("IterContLocal2") {
    // TODO simplify case expressions
    // TODOlater: simplify control-flow by some limited duplication, to avoid mostly useless and complicated sharing structures
    //             [Note: after fixing many problems, it's not that complicated anymore, though]
    TestHarness("IterContLocal2", exec = true)
    //TestHarness("IterContLocal2", "0000"::Nil, exec = true)
    //TestHarness("IterContLocal2", "0001"::Nil, exec = true)
  }
  //test("IterContTuple") {
  //  // Q: does it reduce?
  //  TestHarness("IterContTupleBench", exec = true)
  //}
  test("IterMaybe") {
    // Note: generated program used not to terminate! because a parameter was conflated due to mixing branch and control as param key
    
    //TestHarness("IterMaybe", exec = true)
    
    //TestHarness("IterMaybe", "0000"::Nil, exec = false) // FIXME cannot handle this case yet
    
    //TestHarness("IterMaybe", "0001"::Nil, exec = true)
    // ^ FIXME Current limitation in computation of maximalSharedScope, leading to scope extrusion
    //         Note that the error's cause is now somehwat obscured because one of the two bindings gets inlined at AST phase
  }
  test("IterMaybeMin") {
    //TestHarness("IterMaybeMin", exec = true)
    //TestHarness("IterMaybeMin", "0000"::Nil, exec = true) // FIXME case reduction breaks this program!
    TestHarness("IterMaybeMin", "0001"::Nil, exec = true)
  }
  
}
