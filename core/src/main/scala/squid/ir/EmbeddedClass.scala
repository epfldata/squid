package squid
package ir

import utils._
import lang._
import squid.utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.sru.{MethodSymbol => Mtd}
import squid.lang.Base

abstract class EmbeddedClass[B <: Base](val base: B) {
  import base._
  
  val defs: Map[Mtd, Lazy[SomeCode]]
  val parametrizedDefs: Map[Mtd, List[TypeRep] => SomeCode]
  
  def mtd(sym: Mtd) = defs get sym
  
  val Object: { val Defs: Any }
  val Class: { val Defs: Any }
  
}

abstract trait EmbeddedableClass[B <: Base] {
  def embedIn(base: B): EmbeddedClass[base.type]
}

/** Just a small class to help the IDE feel less confused about the @embed macro annotation... */
trait SquidObject extends SquidObjectIn[Base]
trait SquidObjectIn[B <: Base] extends ir.EmbeddedableClass[B] {
  type Lang <: Base
}

