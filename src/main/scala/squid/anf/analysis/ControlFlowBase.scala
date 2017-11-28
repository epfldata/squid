package squid
package anf.analysis

import squid.lang.InspectableBase
import utils._

/**
  * Created by lptk on 05/02/17.
  * 
  * TODO abstract construct for looping, sequence, etc.
  * 
  */
trait ControlFlowBase extends InspectableBase {
  import Predef.QuasiContext
  
  /** Abstract construct for two alternative paths which execution is either one or the other -- never both nor none
    * TODO generalize by having T0 and T1 for the alternatives' types */
  abstract class OneOf[T,C](val original: Code[T,C]) {
    type C0 <: C // Note: upper bound won't really affect anything since IR is contravariant in its context
    type C1 <: C
    val main: Code[T,C0]
    val alt: Code[T,C1]
    val rebuild: (Code[T,C0],Code[T,C1]) => Code[T,C]
  }
  class OneOfUniform[T,C](original: Code[T,C], val main: Code[T,C], val alt: Code[T,C])(val rebuild: (Code[T,C],Code[T,C]) => Code[T,C]) extends OneOf[T,C](original) {
    type C0 = C
    type C1 = C
  }
  
  object OneOf {
    def unapply[T,C](q: Code[T,C]): Option[OneOf[T,C]] = unapplyOneOf[T,C](q)
  }
  def unapplyOneOf[T,C](q: Code[T,C]): Option[OneOf[T,C]] = q match {
      
    case code"if ($cond) $thn else $els : $t" => Some(new OneOfUniform(q.asInstanceOf[Code[t.Typ,C]],thn,els)((thn, els) => code"if ($cond) $thn else $els")
      .asInstanceOf[OneOf[T,C]]) // Casts, needed because Scala does not know that T =:= t ; note that if we omit the one for `q`, Any is inferred and we don't get the right type implicit!!
      
    case code"($opt:Option[$to]).fold[$tf]($ifEmpty)(x => $body)" =>
      val rebuild_f = (ifEmpty:Code[tf.Typ,C], body:Code[tf.Typ,C{val x: to.Typ}]) => code"$opt.fold($ifEmpty)(x => $body)"
      Some(new OneOf[tf.Typ,C](q.asInstanceOf[Code[tf.Typ,C]]) {
        type C0 = C
        type C1 = C{val x: to.Typ}
        val main = ifEmpty
        val alt = body
        val rebuild = rebuild_f
      }.asInstanceOf[OneOf[T,C]])
    case _ => None
  }
  
  
}


