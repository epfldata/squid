package stagerwr
//package compiler

import squid.utils._
import squid.ir._
import squid.lang._
import squid.anf.analysis
import squid.anf.transfo
import example.VarNormalizer
import squid.quasi.SimpleReps // TODO move to main Squid

/**
  * Created by lptk on 13/06/17.
  */
object Embedding
  //extends squid.ir.SimpleANF
  extends squid.ir.SchedulingANF
  with ScalaCore
  with ClassEmbedder with OnlineOptimizer with analysis.BlockHelpers with StandardEffects
  with SimpleReps
{
  object Desug extends Desugaring
  object Norm extends SelfTransformer with transfo.StandardNormalizer
    //
    with VarNormalizer
    with transfo.LogicNormalizer
    with transfo.EqualityNormalizer 
  {
    import base.Predef._
    import Strm._
    rewrite {
      //case ir"(if ($c) $thn else $els : Strm[$ta])"
      case code"identity[$xt]($x)" => x
    }
  }
  def pipeline = Desug.pipeline andThen Norm.pipeline
  
  embed(Strm)
  
  
  //intWrapper(0)
  addTransparentMethod(methodSymbol[scala.Predef.type]("intWrapper"))
  //addTransparentMethod(methodSymbol[math.`package`.type]("sqrt"))
  
  // TODO add following -- currently not doing it because scheduling is still suboptimal
  //transparentTyps += typeSymbol[scala.runtime.RichInt]
  
  
  
}

