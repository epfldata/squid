// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
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
  
  // Stopped working in 2.12: overriding value Class in class EmbeddedClass of type AnyRef{val Defs: Any};
  /*
  val Object: { val Defs: Any }
  val Class: { val Defs: Any }
  */
  
}

abstract trait EmbeddedableClass[B <: Base] {
  def embedIn(base: B): EmbeddedClass[base.type]
}

/** Just a small class to help the IDE feel less confused about the @embed macro annotation... */
trait SquidObject extends SquidObjectIn[Base]
trait SquidObjectIn[B <: Base] extends ir.EmbeddedableClass[B] {
  type Lang <: Base
}

