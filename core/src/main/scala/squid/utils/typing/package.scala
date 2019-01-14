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

package squid.utils

import scala.collection.mutable
import scala.reflect.macros.whitebox

package object typing {
  
  // Scala does not have a built-in way to go from, e.g., List[A] to List[B] when implicitly[A <:< B]; this corrects that
  
  // cf. related: https://github.com/scalaz/scalaz/blob/d90a5b568588e44acd35a9d6ae0a4a1baae1aaeb/core/src/main/scala/scalaz/Tag.scala#L7
  def substCo    [A,B,F[+_]](x: F[A])(implicit ev: A <:< B): F[B] = x.asInstanceOf[F[B]]
  def substContra[A,B,F[-_]](x: F[A])(implicit ev: B <:< A): F[B] = x.asInstanceOf[F[B]]
  def subst      [A,B,F[ _]](x: F[A])(implicit ev: A =:= B): F[B] = x.asInstanceOf[F[B]]
  
  def substBoundedCo    [Bnd,A<:Bnd,B<:Bnd,F[+_<:Bnd]](x: F[A])(implicit ev: B <:< A): F[B] = x.asInstanceOf[F[B]]
  def substBoundedContra[Bnd,A<:Bnd,B<:Bnd,F[-_<:Bnd]](x: F[A])(implicit ev: A <:< B): F[B] = x.asInstanceOf[F[B]]
  def substBounded      [Bnd,A<:Bnd,B<:Bnd,F[ _<:Bnd]](x: F[A])(implicit ev: A =:= B): F[B] = x.asInstanceOf[F[B]]
  
  //implicit def singletonIsSingleton[A<:Singleton,B<:A]: A =:= B =
  // ^ this is less general than the following:
  /** Scala fail to see that when `T <: x.type`, then `T == x.type` */
  implicit def singletonIsSingleton[A<:Singleton,B](implicit ev: B <:< A): A =:= B = 
    =:=.tpEquals[A].asInstanceOf[A =:= B]
  
  
  // Helpers for first-class-polymorphism:
  
  trait Poly1[F[_]] { def apply[A](x:F[A]):F[A] }
  object Poly1 { def identity[F[_]] = new Poly1[F] { def apply[T](x:F[T]):F[T]=x } }
  
  trait Poly2[F[_,_]] { def apply[A,B](x:F[A,B]):F[A,B] }
  object Poly2 { def identity[F[_,_]] = new Poly2[F] { def apply[A,B](x:F[A,B]):F[A,B]=x } }
  
  type Poly[F[_]] = Poly1[F]
  val Poly = Poly1
  
  
  // Helper for singleton types:
  
  object singleton {
    import scala.language.experimental.macros
    import scala.reflect.macros.whitebox
    
    def scope: Any = macro `scope macro`
    
    def `scope macro`(c: whitebox.Context): c.Tree = {
      val c2 = c.asInstanceOf[reflect.macros.runtime.Context with whitebox.Context]
      import c2.{universe => u2}
      val ctx: c2.universe.analyzer.Context = c2.callsiteTyper.context
      
      val syms2 = ctx.outer.enclosingContextChain.flatMap { ctx =>
        var syms = mutable.Buffer.empty[u2.TermName -> u2.TermSymbol]
        new u2.Traverser {
          override def traverse(tree: u2.Tree): Unit = tree match {
            case d:u2.ValDef 
              if d.symbol.isInitialized
              && d.symbol.isTerm
            =>
              syms += d.name -> d.symbol.asTerm
            case _ => super.traverse(tree)
          }
        } traverse ctx.tree
        syms
      }.groupBy(_._1).map(_._2.head._2).toList
      
      import c.universe._
      val syms = syms2.asInstanceOf[List[TermSymbol]]
      val tpe = c.typecheck(tq"{..${syms.map{ sym => q"type ${sym.name.toTypeName} = ${internal.singleType(NoPrefix,sym)}" }}}", c.TYPEmode).tpe
      
      import internal.decorators._
      q"()".setType(tpe)
    }
    
  }
  
}
