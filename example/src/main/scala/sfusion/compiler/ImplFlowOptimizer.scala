package sfusion
package compiler

import squid.utils._
import squid._
import squid.ir._
import impl._

/*

Seems we need a Transformer interface that allows retrieving the definition of a term,
but to be sound it would have to collaborate closely with the rewriting engine 
  so we cannot access definitions that have been rewritten and no longer exist
  and so we access those that are new and result from a rewriting

Then we could have patterns like:
  case ir"zip[$ta,$tb](${Linear(l0)}, ${Linear(l1)})" =>
Where extractor Linear.unapply accesses the current definitions map
Extracted Linear objects should ideally also contain effects information about what happens between the term and the current rewriting point
Additionally, it would be nicest to have a way to alter the external extarcted term as we go...
  but this seems harder, because:
    would have to rely on some side effects or the `rewrite` syntax would have to be changed 
    enforcing context safety would be tricky


Should ImplFlowOptimizer be bottom-up or top-down??
  cf. zip(zip(linear,linear),linear)
  
  

*/

/**
  * Created by lptk on 12/06/17.
  */
//class ImplOptimizer { self: Compiler =>
//  ImplOptim2
//}
trait ImplFlowOptimizer extends CodeTransformer { self =>
  val base: anf.analysis.BlockHelpers
  import base.Predef._
  import base.InspectableCodeOps
  import base.{AsBlock,WithResult,MethodApplication}
  import base.Val
  
  def transform[T,C](code: Code[T,C]): Code[T,C] = {
    //aux(code, Map())
    code
  }
  //case class Linear[A](xs: IR[Producer[A],?])
  class Linear[A](xs: Code[Producer[A],?])
  //private def aux[T,C](code: IR[T,C], linear: Map[Val,]): IR[T,C] = { code }
  
  
}

