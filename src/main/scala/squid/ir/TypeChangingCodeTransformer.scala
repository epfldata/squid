package squid
package ir

import utils._

trait TypeChangingCodeTransformer extends CodeTransformer { self =>
  import base._
  import Quasiquotes._
  def transform[T,C](code: Code[T,C]): Code[T,C] = {
    val T = code.typ
    transformChangingType(code) match {
      case code"$code: $$T" => code
      case newCode =>
        System.err.println(s"Top-level type ${T.rep} cannot be changed to ${newCode.typ.rep}; in: $code ~> $newCode")
        code
    }
  }
  def transformChangingType[T,C](code: Code[T,C]): Code[_,C]
}
