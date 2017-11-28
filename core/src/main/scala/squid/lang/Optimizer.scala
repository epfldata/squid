package squid.lang

trait Optimizer {
  val base: InspectableBase
  import base._
  protected def pipeline: Rep => Rep
  //final def optimizeRep(pgrm: Rep): Rep = pipeline(pgrm)
  final def optimizeRep(pgrm: Rep): Rep = { // TODO do this Transformer's `pipeline`......?
    val r = pipeline(pgrm)
    if (!(r eq pgrm)) substitute(r) else r  // only calls substitute if a transformation actually happened
  }
  final def optimize[T,C](pgrm: Code[T,C]): Code[T,C] = `internal Code`[T,C](optimizeRep(pgrm.rep))
  
  def wrapOptim[A](id: String)(code: => A) = code
  
  
  def setContext(src:String) = ()
  
}
