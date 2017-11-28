package squid
package anf.transfo

import utils._
import ir._
import utils.Debug.show

/**
  * Created by lptk on 08/02/17.
  * 
  * TODO use a `referentiallyTransparent` method, typically provided by an effect
  * 
  */
trait DeadCodeElimination extends FixPointRuleBasedTransformer with BottomUpTransformer { self =>
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  def referentiallyTransparent(r: base.Rep): Bool = true // !!!
  
  rewrite {
    
    case code"val x: $xt = $init; $body: $bt" if referentiallyTransparent(init.rep) =>
      body subs 'x -> Abort()
      
  }
  
}
