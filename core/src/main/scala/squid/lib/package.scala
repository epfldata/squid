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

import utils._

/** This contains the virtualized definitions of core Scala constructs such as if-then-else's, loops and variables. */
package object lib {
  
  @transparent // Note: `IfThenElse` is NOT @transparencyPropagating as it executes the closures it is passed
  def IfThenElse[A](cond: Boolean, thn: => A, els: => A): A =
    if (cond) thn else els
  
  @transparent
  def While(cond: => Boolean, loop: => Unit): Unit =
    while (cond) loop
  
  @transparencyPropagating
  def Imperative[A](effects: Any*)(result: A): A = result
  
  @inline @transparent def And(lhs: Boolean, rhs: => Boolean) = lhs && rhs
  @inline @transparent def Or(lhs: Boolean, rhs: => Boolean) = lhs || rhs
  
  
  final class ThunkParam private[lib]()
  private val ThunkParam = new ThunkParam
  def ThunkArg: ThunkParam = ThunkParam
  
  
  abstract class MutVar[A] {
    def := (that: A) : Unit
    def ! : A
    override def equals(that: Any) = that |>? { case v: MutVar[_] => this.! == v.! } Else false
    override def toString = s"Var(${this!})"
  }
  object MutVar {
    def apply[A](init: A): MutVar[A] = new MutVar[A] {
      private[this] var cur = init
      def := (that: A) = cur = that
      def ! = cur
    }
  }
  
  /** Used in ReinterpreterToScala when a local variable "escapes", to preserve the validity and semantics of the program. */
  class MutVarProxy[A](get: => A, set: A => Unit) extends MutVar[A] {
    def := (that: A) = set(that)
    def ! = get
  }
  
  // More confusing than useful, especially since it seems to be automatically imported along with Var:
  //implicit def readVar[A](v: Var[A]): A = v!
  
  
  @transparencyPropagating
  def uncurried0[b](f: => b): () => b =
    () => f
  
  @transparencyPropagating
  def uncurried1[a, b](f: a => b): a => b =   // Not actually used, just here for syntactic completeness ^_^
    (x1) => f(x1)
  
  @transparencyPropagating
  def uncurried2[a1, a2, b](f: a1 => a2 => b): (a1, a2) => b =
    (x1, x2) => f(x1)(x2)
  
  @transparencyPropagating
  def uncurried3[a1, a2, a3, b](f: a1 => a2 => a3 => b): (a1, a2, a3) => b =
    (x1, x2, x3) => f(x1)(x2)(x3)
  
  @transparencyPropagating
  def uncurried4[a1, a2, a3, a4, b](f: a1 => a2 => a3 => a4 => b): (a1, a2, a3, a4) => b =
    (x1, x2, x3, x4) => f(x1)(x2)(x3)(x4)
  
  @transparencyPropagating
  def uncurried5[a1, a2, a3, a4, a5, b](f: a1 => a2 => a3 => a4 => a5 => b): (a1, a2, a3, a4, a5) => b  =
    (x1, x2, x3, x4, x5) => f(x1)(x2)(x3)(x4)(x5)
  
  
  @transparent def nullValue[T] = null.asInstanceOf[T]
  
  /** Communicates the intention that this null value is never checked; mainly used to initialize variables with a value
    * that is never supposed to be accessed. */
  @transparent def uncheckedNullValue[T] = null.asInstanceOf[T]
  
  
  /** A dummy function to be used by internal compiler passes to hold temporary code; mainly used to avoid hygiene
    * problems arising from recursive extrusion (until hygienic context polymorphism is implemented). */
  @transparencyPropagating def placeHolder[T](id: String): T =
    throw new AssertionError(s"Tried to execute `$id` placeholder, which was not supposed to be compiled into final program.")
  
  
  final class DummyRecord
  
  import scala.annotation.{StaticAnnotation, compileTimeOnly}
  class ExtractedBinder extends StaticAnnotation
  
}
