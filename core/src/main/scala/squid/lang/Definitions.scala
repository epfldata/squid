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

package squid.lang

import squid.utils._

/** A set of types and methods for manipulating class, object, field, and method definitions using Squid.
  * This is notably used as the output of the `@lift` macro. */
trait Definitions extends Base {
  
  type FieldGetter <: MtdSymbol
  type FieldSetter  <: MtdSymbol
  
  // TODO impl monomorphization of classes and methods
  //   For monomorphized classes, we need to transform all the type references everywhere... so the process will take
  //   a bunch of other external code that uses the class and adapt it, too.
  
  object TopLevel extends Scope {
    type Scp = Any
    val members = Nil
  }
  trait Scope { outerScope =>
    type Scp
    
    sealed abstract class Member
    val members: List[Member]
    
    trait Parameterized {
      def tparams: List[TypParam]
      lazy val typeParams: List[CodeType[_]] =
        tparams.map(tp => CodeType(staticTypeApp(tp, Nil)))
    }
    
    trait ClassWithObject[C] extends Clasz[C] {
      val companion: Some[outerScope.Object[_]]
    }
    trait ClassWithoutObject[C] extends Clasz[C] {
      val companion: None.type = None
    }
    trait ObjectWithClass[C] extends Object[C] {
      val companion: Some[outerScope.Clasz[_]]
    }
    trait ObjectWithoutClass[C] extends Object[C] {
      val companion: None.type = None
    }
    
    type AnyObject = Object[_]
    trait ObjectOf[+C] {
      val name: String
    }
    //abstract class Object[C: CodeType](val name: String, val init: Code[Unit,Scp]) extends ClassOrObject[C] with ObjectOf[C] {
    abstract class Object[C: CodeType](val name: String) extends ClassOrObject[C] with ObjectOf[C] {
      type Scp = outerScope.Scp
      val companion: Option[outerScope.Clasz[_]]
      //val constructor: Method[Unit,Scp] { val typParam: Nil.type; val vparams: Nil.type }
      val constructor: ObjectConstructor
      def initCode: constructor.body.type = constructor.body
      
      override def toString = s"object $name"
    }
    type AnyClasz = Clasz[_]
    /* Note: in Scala 2.11, naming this Class results in strange failures, as in:
     *   java.lang.NoClassDefFoundError: squid/lang/Definitions$Scope$Class (wrong name: squid/lang/Definitions$Scope$class) */
    //abstract class Clasz[C: CodeType](val name: String, val tparams: List[TypParam]) extends ClassOrObject[C] with Parameterized {
    abstract class Clasz[C: CodeType](val name: String) extends ClassOrObject[C] with Parameterized {
      val companion: Option[outerScope.Object[_]]
      val self: Variable[C]
      def tparams: constructor.tparams.type = constructor.tparams
      
      override def toString = s"class $name${if (tparams.isEmpty) "" else tparams.mkString("[",",","]")}"
    }
    abstract class ClassOrObject[C](implicit val C: CodeType[C]) extends Member with Scope {
      type Scp <: outerScope.Scp
      
      // TODO should have special ctor method(s)...
      
      val name: String
      val parents: List[CodeType[_]]
      val constructor: Method[Unit,_]
      val fields: List[Field[_]]
      val methods: List[Method[_,_]]
      
      lazy val members: List[Member] = fields ::: methods
      
      abstract class FieldOrMethod[A](implicit val A: CodeType[A]) extends Member {
        val symbol: MtdSymbol
      }
      type AnyField = Field[_]
      /** If `set` is empty, this is an immutable field.
        * If `get` is empty, this is a private[this] field.
        * If `init` is empty, this is a parameter. */
      class Field[A0: CodeType](
       val name: String,
       val get: FieldGetter,
       //val get: Option[FieldGetter],
       val set: Option[FieldSetter],
       val init: Option[Code[A0,Scp]]
     ) extends FieldOrMethod[A0] {
        type A = A0
        val symbol: MtdSymbol = get
        //val symbol: MtdSymbol = get.getOrElse(???)
        
        //println(s"FIELD $this")
        
        override def toString =
          s"${if (set.isDefined) "var" else "val"} ${symbol}: ${A.rep} = ${
            init.fold("<param>")(i => showRep(i.rep))}"
      }
      type AnyMethod[S <: Scp] = Method[_, S]
      class Method[A0: CodeType, S <: Scp](
        val symbol: MtdSymbol,
        val tparams: List[TypParam],
        val vparamss: List[List[Variable[_]]],
        val body: Code[A0,S]
      ) extends FieldOrMethod[A0] with Parameterized {
        type Scp = S
        type A = A0
        
        //println(s"METHOD $this")
        
        override def toString = s"def ${symbol}[${tparams.mkString(",")}]${vparamss.map(vps => vps.map(vp =>
          //s"${vp.`internal bound`}: ${vp.Typ.rep}"
          s"$vp"
        ).mkString("(",",",")")).mkString}: ${A.rep} = ${showRep(body.rep)}"
      }
      private lazy val UnitType = staticTypeApp(loadTypSymbol("scala.Unit"),Nil)
      class ObjectConstructor(symbol: MtdSymbol, body: Code[Unit,Scp])
      extends Method[Unit,Scp](symbol, Nil, Nil, body)(CodeType(UnitType)) {
        override val vparamss: Nil.type = Nil
        override val tparams: Nil.type = Nil
      }
      
      // A helper for creating Field objects; used by the `@lift` macro
      def mkField(name: String, get: MtdSymbol, set: Option[MtdSymbol], init: Option[Rep])(typ: TypeRep): Field[_] =
      //def mkField(name: String, get: Option[MtdSymbol], set: Option[MtdSymbol], init: Option[Rep])(typ: TypeRep): Field[_] =
        new Field[Any](name,
          get.asInstanceOf[FieldGetter],
          //get.map(_.asInstanceOf[FieldGetter]),
          set.map(_.asInstanceOf[FieldSetter]),init.map(Code(_)))(CodeType[Any](typ))
      
      def showWithBody: String = s"$toString${
        if (constructor.vparamss.isEmpty) "" else constructor.vparamss.map(vps =>
          //vps.map(vp => vp)
          vps.mkString("",",","")
        ).mkString("(",",",")")
      } {${if (members.isEmpty) "" else members.map("\n  "+_).mkString}${
        showRep(constructor.body.rep).splitSane('\n').map("\n  "+_).mkString
      }\n}"
      //} {${if (members.isEmpty) "" else members.map("\n  "+_).mkString+"\n"}}"
      
      // TODO an API for modifying these constructs in a safe way...
      /*
      sealed abstract class MethodTransformation[-A]
      case object Remove extends MethodTransformation[Any]
      case class Rewrite[A](newBody: Code[A,Scp]) extends MethodTransformation[A]
      
      //def transform(trans: Map[Method[_],MethodTransformation])
      def transform(trans: List[MethodTransformation[_]]) = ???
      */
      
    }
    
  }
  
}
