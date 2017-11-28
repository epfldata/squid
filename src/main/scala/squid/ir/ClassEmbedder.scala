package squid
package ir

import squid.utils.meta.RuntimeUniverseHelpers
import utils._
import RuntimeUniverseHelpers.sru
import squid.lang.InspectableBase

import collection.mutable

/** TODO handle varargs */
trait ClassEmbedder { baseSelf: InspectableBase =>
  
  protected[squid] var isEmbedding = false
  def embed(cls: EmbeddedableClass[_ >: baseSelf.type]*): Unit = cls map embed
  def embed(cls: EmbeddedableClass[_ >: baseSelf.type]) = {
    assert(!isEmbedding)
    isEmbedding = true
    try {
      val ecls = cls.embedIn(baseSelf)
      methods ++= ecls.defs
      paramMethods ++= ecls.parametrizedDefs mapValues (new ParamMethod(_))
    } finally isEmbedding = false
  }
  protected var methods = Map.empty[sru.MethodSymbol, Lazy[SomeCode]]
  protected var paramMethods = Map.empty[sru.MethodSymbol, ParamMethod]
  
  import ClassEmbedder._
  import ClassEmbedder.Error._
  
  def methodDef(mtd: sru.MethodSymbol, targs: List[TypeRep]): Either[Error, SomeCode] = {
    if (targs isEmpty) methods get mtd match { case Some(m) => if (m.isComputing) Left(Recursive) else Right(m.value)  case None => Left(Missing) }
    else paramMethods get mtd match { case Some(m) => m(targs)  case None => Left(Missing) }
  }
  
  protected class ParamMethod(f: List[TypeRep] => SomeCode) {
    private var computing = false
    def isComputing = computing
    def apply(targs: List[TypeRep]): Either[Error, SomeCode] = {
      if (computing) Left(Recursive)
      else {
        computing = true
        try Right(f(targs))
        finally computing = false
      }
    }
  }
  
}

object ClassEmbedder {
  sealed trait Error
  object Error {
    case object Recursive extends Error
    case object Missing extends Error
  }
}

