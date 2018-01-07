package squid
package ir.fastanf

import utils._

// cannot be sealed unless we put everything into one file...
/*private[fastanf]*/ trait DefOrTypeRep {
  def typ: TypeRep
  def fold[R](df: Def => R, typeRep: TypeRep => R): R
}

sealed abstract class TypeRep extends DefOrTypeRep {
  def typ = this
  def fold[R](df: Def => R, typeRep: TypeRep => R): R = typeRep(this)
  def asFunType: Option[(TypeRep, TypeRep)] = Some(DummyTypeRep, DummyTypeRep) // TODO
}

case object DummyTypeRep extends TypeRep

