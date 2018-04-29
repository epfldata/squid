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

package object utils {
  
  /** An alternative to scala.Nothing that does not have the bad interaction with type inference and implicits. */
  type Bottom <: Nothing // Note: the lower bound >: Nothing seems to be implicitly assumed by the Scala type checker
  
  /** We have Int instead of Integer; why not Bool instead of Boolean? */
  type Bool = Boolean
  
  /** Dotty syntax for intersection types */
  type & [+A,+B] = A with B
  
  import scala.language.existentials
  type ? = t forSome{type t}
  type ! = Nothing
  
  /** For preventing widening of singleton types.
    * See: https://stackoverflow.com/questions/35903100/what-does-t-do-in-scala/35916154#35916154 */
  type Narrow[T] = T{}
  
  /** Tag type to be interpreted by quasiquotes as an existential named [Unknown Context],
    * useful to ensure rewrite rules are fully parametric in the context of the terms they match */
  final class UnknownContext private() // TODO extend <extruded type>
  
  /** Rewrite rules, which are defined on an `Extract` artifact, may need to access the scrutinee,
    * which is thus assumed to be stored in the Rep mapping under the name `SCRUTINEE_KEY`. */
  final val SCRUTINEE_KEY = "__scrutinee__"
  
  
  /** Allows functions taking one by-name parameter to be used on the rhs of |> and such operators. */
  implicit def byNameFun2fun[A,B](f: (=> A) => B): A => B = f(_)
  
  implicit final class Alsoable[T](private val self: T) extends AnyVal {
    
    // TODO rename to just `also`
    @inline def alsoApply(effect_f: T => Unit) = { effect_f(self); self }
    @inline def alsoApply_?(effect_f: PartialFunction[T,Unit]) = { effect_f.runWith(_=>())(self); self }
    
    @inline def alsoDo(effect: Unit) = self
    
    @inline def thenReturn[A](x: A) = x
    @inline def !> [A](x: A) = x
    
  }
  
  
  implicit final class GenHelper[A](private val __self: A) extends AnyVal {
    
    @inline def into [B] (rhs: A => B): B = rhs(__self)
    
    @inline def |> [B] (rhs: A => B): B = rhs(__self)
    @inline def |>? [B] (rhs: PartialFunction[A, B]): Option[B] = rhs andThen Some.apply applyOrElse (__self, Function const None)
    @inline def |>! [B] (rhs: PartialFunction[A, B]): B = rhs(__self)
    
    /** Like |> but expects the function to return the same type */
    @inline def |>= (rhs: A => A): A = rhs(__self)
    @inline def |>=? (rhs: PartialFunction[A, A]): A = rhs.applyOrElse(__self, Function const __self)
    
    /** A lesser precedence one! */
    @inline def /> [B] (rhs: A => B): B = rhs(__self)
    
    /** 
     * A helper to write left-associative applications, mainly used to get rid of paren hell
     * Example:
     *   println(Id(Sym(f(chars))))
     *   println(Id <|: Sym.apply <|: f <|: chars)  // `Sym` needs `.apply` because it's overloaded
     */
    @inline def <|: [B] (lhs: A => B): B = lhs(__self)
    
    def withTypeOf[T >: A](x: T): T = __self: T
    
    @inline def optionUnless(cond: A => Bool): Option[A] = if (!cond(__self)) Some(__self) else None
    
  }
  
  implicit final class LazyGenHelper[A](__self: => A) {
    
    @inline def optionIf(cond: Bool): Option[A] = if (cond) Some(__self) else None
    @inline def optionIf(cond: A => Bool): Option[A] = if (cond(__self)) Some(__self) else None
    
    @inline def optionUnless(cond: Bool): Option[A] = if (!cond) Some(__self) else None
    
  }
  
  
  implicit class OptionHelper[A](private val __self: Option[A]) extends AnyVal {
    /** Like map */
    @inline def Then[B](f: A => B): Option[B] = __self map f
    /** Like getOrElse */
    @inline def Else[B >: A](x: => B): B = __self getOrElse x
    @inline def retainIf(cond: => Bool): Option[A] = if (__self.isDefined && !cond) None else __self
    @inline def retainUnless(cond: => Bool): Option[A] = if (__self.isDefined && cond) None else __self
  }
  def If[A](cond: Boolean)(thn: A) = if (cond) Some(thn) else None
  
  @inline def some[A](x: A): Option[A] = Some(x)
  @inline def none = None
  
  implicit class FunHelper[A,B](val __self: A => B) extends AnyVal {
    def <| (rhs: A): B = __self(rhs)
    def |>: (lhs: A): B = __self(lhs)
  }
  /*
  implicit class FunHelper2[A,B](val __self: (=>A) => B) extends AnyVal {
    def <| (rhs: => A): B = __self(rhs)
  }
  */
  
  type |>[A, F[_]] = F[A]
  type \/[+A, +B] = Either[A,B]
  
  def ignore = (_: Any) => ()
  def pairWith[A,B](f: A => B)(x: A) = x -> f(x)
  
  
  implicit class SafeEq[T](private val self: T) extends AnyVal {
    def === (that: T) = self == that
    def =/= (that: T) = self != that
  }
  
  
  implicit class StringOps(private val self: String) extends AnyVal {
    import collection.mutable
    def splitSane(Sep: Char) = {
      val buf = mutable.ArrayBuffer(new StringBuilder)
      for (c <- self) if (c == Sep) buf += new StringBuilder else buf.last append c
      buf.map(_.toString)
    }
    def mapLines(f: String => String) = splitSane('\n') map f mkString "\n"
    def indent(pre: String) = mapLines(pre + _)
    def indent: String = indent("\t")
  }
  
  type -> [+A,+B] = (A,B)
  object -> {
    def unapply[A,B](ab: (A,B)) = Some(ab)
  }
  implicit class Tuple2Helper[A,B](private val self: (A,B)) extends AnyVal {
    @inline def mapFirst[C](f: A => C): (C,B) = (self._1 |> f, self._2)
    @inline def mapSecond[C](f: B => C): (A,C) = (self._1, self._2 |> f)
  }
  
  
  def die = lastWords("Program reached and unexpected state.")
  def lastWords(msg: String) = throw new Exception(s"Internal Error: $msg")
  
  /** Used to make Scala unexhaustivity warnings believed to be spurious go away */
  def spuriousWarning = lastWords("Case was reached that was thought to be unreachable.")
  
  def checkless[A,B](pf: PartialFunction[A,B]): A => B = pf
  
  /** Used when we don't want Scalac to assume that something is true (e.g., pattern guard). */
  @inline def trueButDontTellPlz: Bool = true
  
}
