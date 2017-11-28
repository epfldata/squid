package squid
package feature

import squid.utils.meta.RuntimeUniverseHelpers
import utils.Debug._

class Analyse extends MyFunSuite {
  import DSL.Predef._
  
  test("Simple Analysis") {
    
    val q = code"println(1); var cur = 2; for (i <- 3 to 4) cur += 5; cur - 6"
    
    var sum = 0
    q analyse {
      case Const(n) => sum += n
    }
    
    same(sum, 1 + 2 + 3 + 4 + 5 + 6)
    
  }
  
}
