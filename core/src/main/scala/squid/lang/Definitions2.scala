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

abstract class Definitions2 extends Base { base =>
  
  type FieldGetter <: MtdSymbol
  type FieldSetter  <: MtdSymbol
  
  trait Scope {
    type Scp
    val outer: Option[Scope]
    
    type Clasz = base.Clasz[Scp]
    type Object = base.Object[Scp]
    type WithObject = Clasz {
      val companion: Some[Object]
    }
    type WithClass = Object {
      val companion: Some[Clasz]
    }
    
  }
  object TopLevel extends Scope {
    val outer = None
  }
  sealed abstract class Member
  
  abstract class ClassOrObject[OuterScp] extends Member with Scope {
    type Scp <: OuterScp
    type InstanceType
    val InstanceType: CodeType[InstanceType]
    
    val name: String
    val parents: List[CodeType[_]]
    val init: List[InitStatement[Scp]]
    val fields: List[Field[_]]
    val methods: List[Method[_, _ <: Scp]]
    val companion: Option[ClassOrObject[OuterScp]]
    
    lazy val members: List[Member] = fields ::: methods
    
  }
  abstract class Clasz[OuterScp](val name: String) extends ClassOrObject[OuterScp] with Parameterized {
    val companion: Option[base.Object[OuterScp]]
    val self: Variable[InstanceType]
    //def tparams: constructor.tparams.type = constructor.tparams
    
    override def toString = s"class $name${if (tparams.isEmpty) "" else tparams.mkString("[",",","]")}"
  }
  abstract class Object[OuterScp](val name: String) extends ClassOrObject[OuterScp] {
    val companion: Option[base.Clasz[OuterScp]]
  }
  
  
  abstract class FieldOrMethod[A](implicit val A: CodeType[A]) extends Member {
    type Typ = A
    val symbol: MtdSymbol
  }
  class Field[A: CodeType](
    val name: String,
    val get: FieldGetter,
    val set: Option[FieldSetter]
  ) extends FieldOrMethod[A] {
    val symbol: MtdSymbol = get
    override def toString =
      s"${if (set.isDefined) "var" else "val"} ${symbol}: ${A.rep}"
  }
  
  case class TupledMethod[Arg,Ret,Scp](arg: Variable[Arg], body: Code[Arg => Ret, Scp])
  
  class Method[Ret: CodeType, S](
    val symbol: MtdSymbol,
    val tparams: List[TypParam],
    val vparamss: List[List[Variable[_]]],
    val body: Code[Ret,S]
  ) extends FieldOrMethod[Ret] with Parameterized {
    type Scp = S
    
    def tupled(targs: List[CodeType[_]]): TupledMethod[_,Ret,Scp] = ???
    
    override def toString = s"def ${symbol}[${tparams.mkString(",")}]${vparamss.map(vps => vps.map(vp =>
      //s"${vp.`internal bound`}: ${vp.Typ.rep}"
      s"$vp"
    ).mkString("(",",",")")).mkString}: ${A.rep} = ${showRep(body.rep)}"
  }
  
  trait Parameterized {
    def tparams: List[TypParam]
    val vparamss: List[List[Variable[_]]]
    
    lazy val typeParams: List[CodeType[_]] =
      tparams.map(tp => CodeType(staticTypeApp(tp, Nil)))
  }
  
  
  sealed abstract class InitStatement[Scp]
  case class FieldInit[A,Scp](fi: Field[A], value: Code[A,Scp]) extends InitStatement[Scp]
  case class Effect[Scp](cde: Code[Unit, Scp]) extends InitStatement[Scp]
  
  
  
  
}
