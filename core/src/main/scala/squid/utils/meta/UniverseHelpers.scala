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
package utils
package meta

/** Generic helpers for reflection on Universe. */
trait UniverseHelpers[U <: scala.reflect.api.Universe] {
  val uni: U
  import uni._
  
  val Any = typeOf[Any]
  val AnyRef = typeOf[AnyRef]
  val Nothing = typeOf[Nothing]
  val Null = typeOf[Null]
  val Unit = typeOf[Unit]
  val Boolean = typeOf[Boolean]
  // Can't name pattern variables with a cap letter :-/
  //lazy val List(Any, AnyRef, Nothing, Unit, Boolean) =
  //  List(typeOf[Any], typeOf[AnyRef], typeOf[Nothing], typeOf[Unit], typeOf[Boolean])
  
  
  val sru: scala.reflect.runtime.universe.type = scala.reflect.runtime.universe
  lazy val srum = sru.runtimeMirror(getClass.getClassLoader)
  
  
  lazy val importer = scala.reflect.runtime.universe.internal.createImporter(uni)
  
  
  def mkTag[A](tpe: Type) = {
    import reflect.api
    scala.reflect.runtime.universe.TypeTag[A](srum, new scala.reflect.api.TypeCreator {
      def apply[U <: api.Universe with Singleton](m: api.Mirror[U]): U#Type = tpe.asInstanceOf[U#Type]
    })
  }
  
  
  lazy val ByNameParamClass = uni.definitions.ByNameParamClass
  lazy val RepeatedParamClass = uni.definitions.RepeatedParamClass // JavaRepeatedParamClass
  
  def typeIfNotNothing(tp: Type) = {
    assert(tp != NoType)
    if (tp <:< Nothing) None else Some(tp)
  }
  
  
  object SelectMember {
    private def getQual(t: Tree): Option[Tree] = t match {
      case q"$a.$m" => Some(a)
      case _ => None
    }
    def unapply(t: Tree): Option[(Tree,Tree)] = (t match {
      case q"$a[..$ts]" if ts.nonEmpty  => getQual(a) map ((_, t))
      case Apply(a, _) => unapply(a)
      case a => getQual(a) map ((_, t))
    }) ensuring(_.map(_._2.symbol != null) getOrElse true, s"[Internal Error] Extracted null symbol for $t")
  }
  
  object MultipleTypeApply {

    def apply(lhs: Tree, targs: List[Tree], argss: List[List[Tree]]): Tree = {
      val tpeApply = if (targs.isEmpty) lhs else TypeApply(lhs, targs)
      argss.foldLeft(tpeApply)((agg, args) => Apply(agg, args))
    }

    def unapply(value: Tree): Option[(Tree, List[Tree], List[List[Tree]])] = value match {
      case Apply(x, y) =>
        Some(x match {
          case MultipleTypeApply(lhs, targs, argss) =>
            (lhs, targs, argss :+ y) // note: inefficient List appension
          case TypeApply(lhs, targs) =>
            (lhs, targs, Nil)
          case _ =>
            (x, Nil, y :: Nil)
        })

      case TypeApply(lhs, targs) =>
        Some((lhs, targs, Nil))

      case _ => None
    }
  }
  
  object ValOrDefDef {
    def unapply(arg: ValOrDefDef) = arg match {
      case ValDef(mods, name, tpt, rhs) =>                   Some(mods, name, Nil,     Nil,     tpt, rhs)
      case DefDef(mods, name, tparams, vparams, tpt, rhs) => Some(mods, name, tparams, vparams, tpt, rhs)
    }
  }
  
  object FunctionType { // TODO complete with all functions types!
    
    val Fun0Sym = typeOf[() => Any].typeSymbol.asType
    val FunSym  = typeOf[(Any) => Any].typeSymbol.asType
    val Fun2Sym = typeOf[(Any, Any) => Any].typeSymbol.asType
    val Fun3Sym = typeOf[(Any, Any, Any) => Any].typeSymbol.asType
    val Fun4Sym = typeOf[(Any, Any, Any, Any) => Any].typeSymbol.asType
    val Fun5Sym = typeOf[(Any, Any, Any, Any, Any) => Any].typeSymbol.asType
    
    val scalaPackage = FunSym.owner.asType.toType
    
    def unapply(t: Type): Option[Type] = Option(t match {
      case TypeRef(_, Fun0Sym, ret::Nil) => ret
      case TypeRef(_, FunSym, _::ret::Nil) => ret
      case TypeRef(_, Fun2Sym, _::_::ret::Nil) => ret
      case TypeRef(_, Fun3Sym, _::_::_::ret::Nil) => ret
      case TypeRef(_, Fun4Sym, _::_::_::_::ret::Nil) => ret
      case TypeRef(_, Fun5Sym, _::_::_::_::_::ret::Nil) => ret
      case _ => null // converted to None by `Option`
    })
    
    def apply(params: Type*)(ret: Type) = internal.typeRef(scalaPackage, symbol(params.size), params :+ ret toList)
    
    def symbol(arity: Int = 1) = (arity match {
      case 0 => Fun0Sym
      case 1 => FunSym
      case 2 => Fun2Sym
      case 3 => Fun3Sym
      case 4 => Fun4Sym
      case 5 => Fun5Sym
      case _ => throw new UnsupportedOperationException(s"Function type of arity $arity not between 0 and 5")
    }).asType
    
  }
  
  import FunctionType.{FunSym, Fun2Sym, Fun3Sym}
  object AsFun {
    def unapply(x:Type) = x.baseType(FunSym) match {
      case TypeRef(_, FunSym, t0 :: tr :: Nil) => Some(t0,tr)
      case _ => None
    }
  }
  object AsFun2 {
    def unapply(x:Type) = x.baseType(Fun2Sym) match {
      case TypeRef(_, Fun2Sym, t0 :: t1 :: tr :: Nil) => Some(t0,t1,tr)
      case _ => None
    }
  }
  object AsFun3 {
    def unapply(x:Type) = x.baseType(Fun3Sym) match {
      case TypeRef(_, Fun3Sym, t0 :: t1 :: t2 :: tr :: Nil) => Some(t0,t1,t2,tr)
      case _ => None
    }
  }
  
  object PossibleRefinement {
    def unapply(t: Type): Option[(List[Type], Scope)] = t match {
      case RefinedType(bases, scp) => Some(bases -> scp)
      case tp => Some((tp :: Nil) -> internal.newScopeWith())
    }
  }
  
  
  implicit class TreeOps(private val self: Tree) {
    def analyse(pf: PartialFunction[Tree, Unit]) =  {
      new Traverser {
        override def traverse(x: Tree) = pf.applyOrElse(x, super.traverse)
      } traverse self
    }
    def analyseRec(rec_pf: (Tree => Unit) => PartialFunction[Tree, Unit]) =  analyser(rec_pf)(self)
    def transform(pf: PartialFunction[Tree, Tree]) =  {
      new Transformer {
        override def transform(x: Tree) = pf.applyOrElse(x, super.transform)
      } transform self
    }
    def transformRec(rec_pf: (Tree => Tree) => PartialFunction[Tree, Tree]) = transformer(rec_pf)(self)
  }
  
  def transformer(rec_pf: (Tree => Tree) => PartialFunction[Tree, Tree]) = {
    // Scala 2.12 bug reported there: https://github.com/scala/bug/issues/10856
    /*
    new Transformer {
      val pf: PartialFunction[Tree, Tree] = rec_pf(transform) // on Scala 2.12, this raises: java.lang.NoSuchMethodError: squid.utils.meta.UniverseHelpers$$anon$5.pf()Lscala/PartialFunction
      // ^ solved if we make it a def
      override def transform(x: Tree) = pf.applyOrElse(x, super.transform)
    } transform _
    */
    val t = new Transformer {
      val pf: PartialFunction[Tree, Tree] = rec_pf(transform)
      override def transform(x: Tree) = pf.applyOrElse(x, super.transform)
    }
    t transform _
  }
  def analyser(rec_pf: (Tree => Unit) => PartialFunction[Tree, Unit]) = {
    // cf Scala 2.12 bug:
    /*
    new Traverser {
      val pf: PartialFunction[Tree, Unit] = rec_pf(traverse)
      override def traverse(x: Tree) = pf.applyOrElse(x, super.traverse)
    } traverse _
    */
    val t = new Traverser {
      val pf: PartialFunction[Tree, Unit] = rec_pf(traverse)
      override def traverse(x: Tree) = pf.applyOrElse(x, super.traverse)
    }
    t traverse _
  }
  
  
  def untypeTreeShape(t: Tree) = {
    // TODO
    t
  }
  
  /** A symbol's fullName may be ambiguous; for example, a.X.Y can refer to a type Y in a class a.X, or in an object a.X
    * This encodes Symbol paths using a static prefix, then #-separated names, where the name has '$' appended if it
    * refers to a term. */
  def encodedTypeSymbol(tsym: TypeSymbol) = {
    assert(!tsym.isParameter, s"cannot encode static reference to parameter $tsym")
    def rec(sym: Symbol): String =
      (if (sym.isStatic) sym.fullName
      else rec(sym.owner)+"#"+sym.name)+(if (sym.isModuleClass) "$" else "")
    rec(tsym)
  }
  
  
  // TODO factor relevant code here:
  //def overloadingIndexOf(mtd: MethodSymbol) =
  
  
  def isErroneous(tp: Type) =
    tp.asInstanceOf[scala.reflect.internal.Types#Type].isErroneous
  
  
  object FlagUtils {
    import Flag._
    
    def rmFlagsIn(from: FlagSet, rm: FlagSet): FlagSet = (from.asInstanceOf[Long] & ~rm.asInstanceOf[Long]).asInstanceOf[FlagSet]
    def mkPublic(fs: FlagSet): FlagSet = rmFlagsIn(fs, PRIVATE | PROTECTED | LOCAL)
    def mapFlags(m: Modifiers)(f: FlagSet => FlagSet) = Modifiers(f(m.flags), m.privateWithin, m.annotations)
  
  }
  
}

abstract class UniverseHelpersClass[U <: scala.reflect.api.Universe](val uni: U) extends UniverseHelpers[U]

object RuntimeUniverseHelpers extends UniverseHelpersClass[scala.reflect.runtime.universe.type](scala.reflect.runtime.universe)



