// Copyright 2019 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package squid.ir

import scala.collection.mutable
import squid.utils._

/** A trait to mix into any AST IR to give access to the .! and .bind_! effectful reificatiom features. */
trait EffectfulASTReification extends AST with squid.lang.EffectfulReification {
  
  sealed trait RegisteredRep
  class AutomaticVal(val bound: Rep) extends BoundVal("_auto")(bound.typ, Nil) with RegisteredRep
  class AutomaticEffect(val rep: Rep) extends RegisteredRep
  
  protected var reificationContext = List.empty[mutable.ListBuffer[RegisteredRep]]
  
  def registerBoundRep(r: Rep): BoundVal = {
    val v = new AutomaticVal(r)
    reificationContext.head += v
    v
  }
  def registerEffectRep(r: Rep): Unit = {
    reificationContext.head += new AutomaticEffect(r)
  }
  
  override def wrapConstruct(mkRep: => Rep): Rep =
    wrapEffectfulReification(super.wrapConstruct(mkRep))
  
  def wrapEffectfulReification(mkRep: => Rep): Rep = {
    val oldCtx = reificationContext
    val curCtx = mutable.ListBuffer.empty[RegisteredRep]
    reificationContext = curCtx :: oldCtx
    try {
      val res = mkRep
      val inserted = curCtx.toList
      inserted.foldRight(res) {
        case (v: AutomaticVal, cur) => letin(v, v.bound, cur, cur.typ)
        case (e: AutomaticEffect, Imperative(xs,x)) => Imperative(e.rep +: xs : _*)(x)
        case (e: AutomaticEffect, cur) => Imperative(e.rep)(cur)
      }
    } finally reificationContext = oldCtx
  }
  
  override abstract def lambda(params: List[BoundVal], body: => Rep) = {
    super.lambda(params, wrapEffectfulReification(body))
  }
  
}
