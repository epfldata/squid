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
package feature

import squid.ir.RewriteAbort
import utils._

class TrickyTypes extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Local Type Synonym") {
    
    code"Option.empty[String]" eqt {
      type String = java.lang.String
      code"Option.empty[String]"
    }
    
  }
  
  test("Local Type With Evidence") {
    
    class Lol
    
    assertDoesNotCompile("""
      code"Option.empty[Lol]"
    """)
    
    code"Option.empty[Int]" eqt {
      implicit val LolImpl = codeTypeOf[Int].asInstanceOf[CodeType[Lol]]
      code"Option.empty[Lol]"
    }
    
  }
  
  
  test("Explicit Empty Contexts and Inferred Contexts") {
    
    List[Code[Int,{}]](code"1", code"2", code"3").foldLeft(code"0") { (acc, exp) =>
      code"if ($acc != 0) $acc else $exp"
    }
    
  }
  
  test("Singleton Contexts") {
    
    val v = Variable[Int]
    object M { type C = v.Ctx }
    val c0: Code[Int,M.C] = c"$v + 1"
    val c1: ClosedCode[Int => Int] = c"{$v => $c0}"
    c1 eqt c"{x: Int => x + 1}"
    
  }
  
  
  test("Lambda with Expected Type") {
    import base.Quasicodes._
    
    val c1: Code[Int => Int => Bool => Bool,_] = code{ (s:Int) =>
      val n = 42
      k => { b => b }
    }
    
    eqt(c1.Typ, codeTypeOf[Int => Int => Bool => Bool])
    
  }
  
  
  def foo[T](x:Code[T,{}]) = code"$x==0"
  
  test("Any method called on type parameter") {
    foo(code"42") eqt code"${code"42:Any"} == 0"
    foo(code"42") neqt code"${code"42"} == 0" // Note: Int.== and Any.== have two different method symbols!!
  }
  
  test("Type evidence on non-singleton type") {
    
    eqt(foo(code"123").Typ : CodeType[_ <: Bool], codeTypeOf[Bool])
    // ^ note that this does not yield a `CodeType[Bool]` because of declaration-site variance of Code[_,C] types
    
  }
  
  
  import TrickyTypes._
  
  test("Abstract Types") {
    
    // References to Abstract used to incur a type tag (uninterpretedType fallback), now they should not
    same(typeRepOf[Abstract],
      base.staticTypeApp(
        base.loadTypSymbol("squid.feature.TrickyTypes$#Abstract"), Nil))
        // ^ Note: using "squid.feature.TrickyTypes.Abstract" raises: class squid.feature.TrickyTypes.Abstract not found
    
    same(code"Option.empty[Abstract]".run, None)
    
  }
  
  test("Abstract Type with Type Parameter") {
    
    def foo[A:CodeType] = {
      same(typeRepOf[AbsT[A]],
        base.staticTypeApp(base.loadTypSymbol("squid.feature.TrickyTypes$#AbsT"), typeRepOf[A]::Nil))
      code"Option.empty[AbsT[A]]"
    }
    foo[Int] eqt code"Option.empty[AbsT[Int]]"
    
    eqt(codeTypeOf[Id[Int]], codeTypeOf[Int])
    
  }
  
  test("Higher-Kinded Abstract Types") {
    
    same(typeRepOf[HK[Id]],  // note: doesn't dealias Id to a type lambda – type lambdas are not supported
      base.staticTypeApp(base.loadTypSymbol("squid.feature.TrickyTypes$#HK"),
        base.staticTypeApp(base.loadTypSymbol("squid.feature.TrickyTypes$#Id"), Nil)::Nil))
    
  }
  
  test("Modular Metaprogramming") {
    
    val mm = new ModularMetaprogImpl[Int]
    eqt(mm.cde, code"Option.empty[Int]")
    eqt(mm.cde2, code"Option.empty[ModularMetaprog#Typ2]")
    // TODO only embed abstract types when static path to them is static?
    //      indeed, it would be more useful for programmers to reject the definition of cde2 above than accept it
    
  }
  
  import scala.reflect.runtime.{universe => sru}
  def sameType[T:sru.WeakTypeTag](cde: OpenCode[Any]) =
    assert(cde.Typ.rep.tpe =:= sru.weakTypeOf[T], s"${cde.Typ.rep.tpe} =/= ${sru.weakTypeOf[T]}")
  
  test("Path-Dependent Types") {
    
    sameType[Option[pdt.Typ]]             (code"Option.empty[pdt.Typ]")
    sameType[Option[sru.TypeTag[pdt.Typ]]](code"Option.empty[sru.TypeTag[pdt.Typ]]")
    
    // This one is not considered a static path (though it should b, in principle):
    //sameType[Option[pdt.nestedPdt.Typ]](code"Option.empty[pdt.nestedPdt.Typ]") // nope
    same(code"Option.empty[pdt.nestedPdt.Typ]".toString, "code\"scala.Option.empty[(squid.feature.TrickyTypes.ModularMetaprog)#Typ]\"")
    //sameType[Option[ModularMetaprog#Typ]](code"Option.empty[pdt.nestedPdt.Typ]" alsoApply println)
    //sameType[Option[ModularMetaprog#Typ]](code"Option.empty[pdt.nestedPdt.nestedPdt.Typ]" alsoApply println)
    // ^ for some reason, return false with: 'Option[squid.feature.TrickyTypes.ModularMetaprog#Typ] =/= Option[squid.feature.TrickyTypes.ModularMetaprog#Typ]'
    
    sameType[Option[pdt.NestedModule.type]]    (code"Option.empty[pdt.NestedModule.type]")
    sameType[Option[List[pdt.Typ]]]            (code"Option.empty[pdt.NestedModule.Typ]")
    sameType[Option[List[List[pdt.Typ]]]]      (code"Option.empty[pdt.NestedModule.NestedModule.Typ]")
    sameType[Option[List[List[List[pdt.Typ]]]]](code"Option.empty[pdt.NestedModule.nestedPdt.NestedModule.Typ]")
    
  }
  
  test("Path-Dependent Type Aliases") {
    
    sameType[Option[pdt.Typ]](code"Option.empty[pdtAlias.Typ]")
    sameType[Option[List[pdt.Typ]]](code"Option.empty[pdtAlias.nestedModuleAlias.Typ]")
    sameType[Option[List[pdt.Typ]]](code"Option.empty[pdt.NestedModule.Typ]")
    
  }
  
}

object TrickyTypes {
  
  type Abstract
  type Id[T] = T
  type HK[F[_]]
  type AbsT[T] <: Int
  
  import TestDSL.Predef._
  abstract class ModularMetaprog {
    type Typ
    implicit val Typ: CodeType[Typ]
    lazy val cde = code"Option.empty[Typ]" // Note: here Squid uses the implicit value available
    type Typ2
    lazy val cde2 = code"Option.empty[Typ2]" // Note: here in the absence of implicit, Squid widens the type to ModularMetaprog#Typ2!!
    
    class Foo[A]
    
    val nestedPdt: ModularMetaprog
    object NestedModule extends ModularMetaprogImpl[List[Typ]]
    //object NestedModule extends ModularMetaprogImpl // NOTE: infers type param as Typ because it's the only type implicit in scope! 
    val nestedModuleAlias: NestedModule.type
  }
  class ModularMetaprogImpl[T: CodeType] extends ModularMetaprog {
    type Typ = T
    val Typ = codeTypeOf[T] // Note: in Scala 2.12 (but not 2.11), it is sufficient to write: `implicitly`
    lazy val nestedPdt = new ModularMetaprogImpl[List[T]]
    lazy val nestedModuleAlias = NestedModule
  }
  
  val pdt: ModularMetaprog = new ModularMetaprogImpl[Int]
  val pdtAlias: pdt.type = pdt
  
}
