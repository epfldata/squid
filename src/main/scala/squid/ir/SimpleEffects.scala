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

import squid.lib.transparencyPropagating
import squid.lib.transparent
import utils._

import collection.mutable

/** Rudimentary (simplistic?) effect system for AST.
  * 
  * Methods and types are associated with binary "referential transparency" info.
  * The central approximation is that "referentially-transparent" methods are those which execution is referentially 
  * transparent as long as all arguments (including closures) passed to them have no effect (immediate or latent).
  * 
  * Latent effects are effects delayed by lambda abstraction. We only keep track one level of 'latency' (collapsing all further levels).
  * As a result, `(() => () => println)()` is currently considered impure, although the latent effect is not actually executed.
  * 
  * Referentially-transparent types are (immutable) types that own only referentially-transparent methods (except those
  * registered explicitly in `opaqueMtds`).
  * Also, values of these types are assumed not to contain latent effects. For example, `Function[Int,Int]` is not
  * ref-transp because some values like `(_:Int)+readInt` contain latent effects.
  * 
  * Finally, "referential-transparency-propagating" methods are referentially-transparent methods that propagate the
  * referential transparency of their arguments.
  * 
  * TODO add @read effects: can be dead-code removed, but not moved around
  *   also, a @read method applied to an immutable (transparent) type can be considered transparent! (cf. can solve `size` problem below)
  * TODO in the same vein, have semi-transparent/self-contained types
  * 
  * TODO a mechanism to add special quasiquote-based rules for purity; for example for `scala.collection.SeqLike.size`, which is not always pure!
  */
trait SimpleEffects extends AST {
  
  // TODO synchronize accesses to these...?
  protected val transparentMtds = mutable.Set[MtdSymbol]()
  protected val opaqueMtds = mutable.Set[MtdSymbol]()
  protected val transparentTyps = mutable.Set[TypSymbol]()
  
  protected val transparencyPropagatingMtds = mutable.Set[MtdSymbol]()
  protected val nonTransparencyPropagatingMtds = mutable.Set[MtdSymbol]()
  def isTransparencyPropagatingMethod(m: MtdSymbol): Bool = {
    transparencyPropagatingMtds(m) || !nonTransparencyPropagatingMtds(m) && {
      val r = m.annotations.exists(_.tree.tpe <:< TranspPropagAnnotType)
      (if (r) transparencyPropagatingMtds else nonTransparencyPropagatingMtds) += m
      r
    }
  }
  
  def addTransparentMethod(m: MtdSymbol): Unit = transparentMtds += m
  def isTransparentMethod(m: MtdSymbol): Bool = {
    transparentMtds(m) || !opaqueMtds(m) && {
      val r = (
        m.annotations.exists(_.tree.tpe <:< TranspAnnotType)
        || (transparentTyps(m.owner.asType) optionIf (m.owner.isType) Else false)
        || (m.overrides exists (s => s.isMethod && isTransparentMethod(s.asMethod)))
        || m.isAccessor && {val rst = m.typeSignature.resultType.typeSymbol; rst.isModule || rst.isModuleClass }
      )
      (if (r) transparentMtds else opaqueMtds) += m
      r
    }
  }
  def isOpaqueMethod(m: MtdSymbol): Bool = !isTransparentMethod(m)
  
  def isTransparentType(m: TypSymbol) = transparentTyps(m)
  
  /** Allows for caching effects in the `Rep`. Implement with just `effect(r)` for no caching to happen. */
  def effectCached(r: Rep): SimpleEffect
  def effect(r: Rep): SimpleEffect = dfn(r) match {
    case Abs(p,b) => (b|>effectCached).prev
    case MethodApp(s,m,ts,pss,rt) =>
      val propag = m |> isTransparencyPropagatingMethod
      lazy val e = (s +: pss.flatMap(_.reps)).map(effectCached).fold(SimpleEffect.Pure)(_ | _)
      if (propag || isTransparentMethod(m) 
        || e == SimpleEffect.Pure && isTransparentType(s.typ.typeSymbol.asType)
        // ^ heuristic: if the sub-expressions are pure and the receiver is of transparent type (like Int), we assume the expression is pure
        // Note that the first condition alone is not sufficient; see `scala.Predef.println` where the only sub-expr `scala.Predef` is pure
      ) {
        if (propag) e else e.next
      } else SimpleEffect.Impure
    // Cannot assume that a bound value of an opaque type does not hide a latent effect:
    case bv: BoundVal if !isTransparentType(bv.typ.typeSymbol.asType) => SimpleEffect.Latent
    case Ascribe(r,_) => r|>effectCached
    case Module(r,_,_) => r|>effectCached
    case _:ConstantLike | _: BoundVal | StaticModule(_) | NewObject(_) | RecordGet(_,_,_) | _:Hole | _:SplicedHole => SimpleEffect.Pure
  }
  
  
  import scala.reflect.runtime.{universe=>sru}
  
  // This one not in `StandardEffects` because it can be viewed as a fundamental implementation detail of the curry encoding: 
  //transparencyPropagatingMtds ++= sru.typeOf[squid.lib.`package`.type].members.filter(_.name.toString startsWith "uncurried").map(_.asMethod)
  // ^ it is no more necessary because now the methods are annotated directly!
  
  val TranspAnnotType = sru.typeOf[transparent]
  val TranspPropagAnnotType = sru.typeOf[transparencyPropagating]
  
}

// TODO don't actually recreate values all the time -- cache the 4 values!
case class SimpleEffect(immediate: Bool, latent: Bool) {
  def | (that: SimpleEffect) = SimpleEffect(immediate || that.immediate, latent || that.latent)
  def isBoth = immediate && latent
  def next = SimpleEffect(immediate || latent, latent)
  def prev = SimpleEffect(false, immediate || latent)
}
object SimpleEffect {
  val Pure = SimpleEffect(false,false)
  val Impure = SimpleEffect(true,true)
  val Latent = SimpleEffect(false,true)
}



/* TODO add types "scala.TupleX", method "scala.Predef.$conforms"
 * Note: should NOT make "squid.lib.Var.apply" trivial since it has to be let-bound for code-gen to work */
trait StandardEffects extends SimpleEffects {
  
  import scala.reflect.runtime.{universe=>sru}
  import reflect.runtime.universe.TypeTag
  
  def typeSymbol[T:TypeTag] = implicitly[TypeTag[T]].tpe.typeSymbol.asType
  def methodSymbol[T:TypeTag](name: String, index: Int = -1) = {
    val tpe = implicitly[TypeTag[T]].tpe
    val alts = tpe.member(sru.TermName(name)).alternatives.filter(_.isMethod)
    val r = if (alts.isEmpty) throw new IllegalArgumentException(s"no $name method in $tpe")
      else if (alts.size == 1) alts.head
      else {
        require(index >= 0, s"overloaded method $name in $tpe")
        alts(index)
      }
    r.asMethod
  }
  
  //transparentTyps += sru.typeOf[squid.lib.`package`.type].typeSymbol.asType
  // ^ no more necessary; methods are now annotated
  
  //transparentTyps += typeSymbol[Unit] // add this one?
  transparentTyps += typeSymbol[Null]
  transparentTyps += typeSymbol[Bool]
  transparentTyps += typeSymbol[Char]
  transparentTyps += typeSymbol[Short]
  transparentTyps += typeSymbol[Int]
  transparentTyps += typeSymbol[Long]
  transparentTyps += typeSymbol[Float]
  transparentTyps += typeSymbol[Double]
  transparentTyps += typeSymbol[String]
  transparentTyps += typeSymbol[Symbol]
  transparentTyps += typeSymbol[Symbol.type]
  
  // TODO should make these @read but not pure:
  //pureTyps += sru.typeOf[Any].typeSymbol.asType // for, eg, `asInstanceOf`, `==` etc.
  transparentMtds += methodSymbol[Any]("asInstanceOf")
  
  // It's not a good idea to make FunctionN a transparent type because it can have latent effects
  // TODO: However it would be nice to have things like `andThen` be transparency-propagating
  /*{
    def addFunTyp(tp: sru.Type) = {
      transparentTyps += tp.typeSymbol.asType
      opaqueMtds += tp.member(sru.TermName("apply")).asMethod
    }
    addFunTyp(sru.typeOf[Function0[Any]])
    addFunTyp(sru.typeOf[Function1[Any,Any]])
    addFunTyp(sru.typeOf[Function2[Any,Any,Any]])
    addFunTyp(sru.typeOf[Function3[Any,Any,Any,Any]])
  }*/
  
  private[this] val notTransp = Set(methodSymbol[Object]("equals"),methodSymbol[Object]("hashCode"),methodSymbol[Object]("$eq$eq"),methodSymbol[Object]("$hash$hash"))
  // ^ These should not be included by the following function, as they can be arbitrarily overridden, thereby becoming opaque (eg: equals for a mutable object)
  // ^ Note that this is not really necessary anymore, as ModularEmbedding now doesn't load methods from Object anymore (instead preferring Any)
  def allTranspPropag(typ: sru.Type) = typ.members.foreach { t =>
    if (t.isMethod || t.alternatives.size > 1) t.alternatives foreach { a =>
      if (a.isMethod && !notTransp(a.asMethod)) transparencyPropagatingMtds += a.asMethod
    }
  }
  
  transparentTyps += typeSymbol[Unit]
  sru.rootMirror.staticPackage("scala").typeSignature.members.foreach { s =>
    if (s.name.toString startsWith "Tuple") {
      if (s.isType) s.asType.toType |> allTranspPropag
      else if (s.isModule) s.typeSignature |> allTranspPropag
    }
  }
  
  transparentTyps += typeSymbol[scala.collection.immutable.Traversable[Any]]
  transparentTyps += typeSymbol[scala.collection.immutable.Seq[Any]]
  transparentTyps += typeSymbol[scala.collection.immutable.Seq.type]
  transparentTyps += typeSymbol[scala.collection.immutable.List[Any]] // Useful to make things like List.map 
  transparentTyps += typeSymbol[scala.collection.immutable.List.type]
  
  /* transparentTyps += typeSymbol[scala.collection.generic.GenericCompanion[List]] // for the `apply`/`empty` methods */
  // ^ this is not right: will register the GenericCompanion symbol (ignoring the List parameter), and thus things like
  // mutable.Set.apply will be considered pure!
  
  // These are not correct, as mutable collections `size` is not referentially-transparent -- TODO use the @read effect
  /*
  {
    val typ = sru.typeOf[scala.collection.GenTraversableOnce[_]]
    pureMtds += typ.member(sru.TermName("size")).asMethod
  }
  
  {
    val typ = sru.typeOf[scala.collection.GenSeqLike[_,_]]
    pureMtds += typ.member(sru.TermName("length")).asMethod
  }
  */
  
  transparentTyps += typeSymbol[Option[Any]]
  transparentTyps += typeSymbol[Some.type]
  transparentTyps += typeSymbol[None.type]
  transparencyPropagatingMtds += methodSymbol[Some.type]("apply")
  // ^ Some(_) is lready known to be transp, but it's actually transpropag too! eg: `Some((x:Int) => readInt)` only has a deferred effect
  
  transparentTyps += typeSymbol[Either[Any,Any]]
  transparentTyps += typeSymbol[Left.type]
  transparentTyps += typeSymbol[Right.type]
  
  
  // Not enabled because it currently makes the closure depend on the input in the tests' flatMap fusion -- case not yet handled
  //transparentMtds += methodSymbol[scala.Predef.type]("wrapString")
  // TODO
  //sru.rootMirror.staticModule("scala.Predef").typeSignature.members.foreach { s =>
  //  if (s.isMethod && (s.name.toString startsWith "wrap")) {
  //    transparentMtds += s.asMethod
  //  }
  //}
  
  transparencyPropagatingMtds += methodSymbol[scala.Predef.type]("identity")
  
}
