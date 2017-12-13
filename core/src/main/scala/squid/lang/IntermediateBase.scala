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
package lang

import squid.utils.meta.RuntimeUniverseHelpers._
import squid.utils.MacroUtils.MacroSetting
import squid.quasi.MetaBases
import utils._

/** An Intermediate Base is one that can still be reinterpreted into yet another Squid Base, using `reinterpret`,
  * and thus can also be ran; by reinterpreting into the dynamic `BaseInterpreter` or by compiling scala trees 
  * obtained from reinterpretation through `MetaBases.ScalaReflectionBase`  */
trait IntermediateBase extends Base { ibase: IntermediateBase =>
  
  // TODO IR and CodeType, irTypeOf, typeRepOf, repType, etc.
  
  
  def repType(r: Rep): TypeRep
  def boundValType(bv: BoundVal): TypeRep
  
  val DefaultExtrudedHandler = (bv: BoundVal) => throw ir.IRException(s"Extruded (free) variable cannot be reinterpreted: $bv")
  
  def reinterpret(r: Rep, newBase: Base)(extrudedHandle: (BoundVal => newBase.Rep) = DefaultExtrudedHandler): newBase.Rep
  
  def nullValue[T: CodeType]: Code[T,{}]
  
  
  //override def showRep(r: Rep) = showScala(r)
  @volatile private var showing = false
  protected def isShowing = showing
  override def showRep(r: Rep) = synchronized { if (showing) super.showRep(r) else try { showing = true; showScala(r) } finally { showing = false } }
  def showScala(r: Rep) = {
    val (newRep,csvals) = separateCrossStageNodes(r)
    val tree = scalaTree(newRep, bv => sru.Ident(sru.TermName(boundValUniqueName(bv))), markHoles = true)
    sru.showCode(tree) + (if (csvals.isEmpty) "" else s" % (${csvals mkString ","})")
  }
  // ^ Note: used to show extruded vals as s"?${bv}?" which looked ugly (as in `?[x:Int]?`)
  
  /** If there are any cross-stage values present in `r`, returns them as a list, and a term representing a function
    * from this list of values to the original `r`; otherwise just return `r`. */
  def separateCrossStageNodes(r: Rep): Rep -> List[Any]
  
  def boundValUniqueName(bv: BoundVal): String
  
  def extractVal(r: Rep): Option[BoundVal]
  
  
  implicit class IntermediateRepOps(private val self: Rep) {
    def typ = repType(self)
  }
  
  /* This used to be an implicit class, as in:
         implicit class IntermediateCodeOps[Typ,Ctx](private val self: Code[Typ,Ctx])
     but we had a problem with the `Typ` function depending on `self`, and making `self` public would expose it as
     an extension method to all code values! 
     Alternatives don't work either (for obscure reasons Scala fails to apply the implicit class), such as:
         implicit class IntermediateCodeOps[Typ,Ctx,S<:Code[Typ,Ctx]](private val self: S)
         implicit class IntermediateCodeOps[Typ,Ctx,S<:Code[Typ,Ctx] with Singleton](private val self: S)
  */
  implicit def IntermediateCodeOps[Typ,Ctx](c: Code[Typ,Ctx]): IntermediateCodeOps[Typ,Ctx,c.type] =
    new IntermediateCodeOps[Typ,Ctx,c.type](c)
  
  class IntermediateCodeOps[Typ,Ctx,S<:Code[Typ,Ctx]](self: S) {
    
    def trep = repType(self.rep)
    
    @deprecated("Use .Typ instead", "0.3.0")
    def typ: CodeType[S#Typ] = `internal CodeType`(trep)
    
    /* Note: making it `def Typ: CodeType[Typ]` would surely be unsound! */
    /** Same as `typ`, but with a capital letter for consistency with the `Typ` type member. */
    def Typ: CodeType[S#Typ] = `internal CodeType`(trep)
    /* ^ this used to be declared in class Code[+T,-C], using an ugly subtype evidence, as:
      // Note: cannot put this in `IntermediateIROps`, because of the path-dependent type
      def Typ(implicit ev: self.type <:< (self.type with IntermediateBase)): CodeType[Typ] = {
        // Ninja path-dependent typing (relies on squid.utils.typing)
        val s: self.type with IntermediateBase = self
        val r: s.Rep = substBounded[Base,self.type,s.type,({type λ[X<:Base] = X#Rep})#λ](rep)
        s.`internal CodeType`(s.repType(r))
      } */
    
    //def Typ: CodeType[self.Typ] = `internal CodeType`(trep)
    /* ^ this definition is more elegant, but makes Scala infer idiotic types that are not reduced enough, such as:
           "inferred existential type TypeChangingCodeTransformer.this.base.CodeType[_582.self.Typ] 
             forSome { val _582: TypeChangingCodeTransformer.this.base.IntermediateCodeOps[T,C]{val self: code.type} }, 
             which cannot be expressed by wildcards" */
    
    
    import scala.language.experimental.macros
    
    def subs[T1,C1](s: => (Symbol, Code[T1,C1])): Code[Typ,_ >: Ctx] = macro quasi.QuasiMacros.subsImpl[T1,C1]
    // ^ Note: why _ >: Ctx ? What if C1 is not Any?
    @MacroSetting(debug = true) def dbg_subs[T1,C1](s: => (Symbol, Code[T1,C1])): Code[Typ,_ >: Ctx] = macro quasi.QuasiMacros.subsImpl[T1,C1]
    
    /** Helper macro to palliate limitations of Scala's type inference when using Variable#substitute: */
    def apply[T](v: Variable[T]) = new {
      // Note: amazingly, using `squid.utils.Bottom` instead of `Nothing` sometimes does not work!
      // Using some existential (even unbounded) does not always work either!
      def ~> [C] (term: Code[T,C]): Code[Typ,Nothing /*_ >: Ctx & C*/] = macro quasi.QuasiMacros.varSubsImpl[C]
      @MacroSetting(debug = true) def dbg_~> [C] (term: Code[T,C]): Code[Typ,Nothing /*_ >: Ctx & C*/] = macro quasi.QuasiMacros.varSubsImpl[C]
    }
    
    def reinterpretIn(newBase: Base): newBase.Code[Typ,Ctx] =
      newBase.`internal Code`(newBase.wrapConstruct( reinterpret(self.rep, newBase)(DefaultExtrudedHandler) ))
    
    /** Executes the code at runtime using Java reflection */
    def run(implicit ev: {} <:< Ctx): Typ = {
      val Inter = new ir.BaseInterpreter
      // ^ Note: making a new one each time is wasteful, but because it extends RuntimeSymbols, which has mutable
      //         caches, the BaseInterpreter is not thread-safe... (and Squid tests are ran in parallel)
      reinterpret(self.rep, Inter)().asInstanceOf[Typ]
    }
    
    /** Compiles and executes the code at runtime using the Scala ToolBox compiler */
    // TODO make `compile` a macro that can capture surrounding vars to fill in existing context dependencies?
    def compile(implicit ev: {} <:< Ctx): Typ = {
      val (newRep,csvals) = separateCrossStageNodes(self.rep)
      val tree = scalaTree(newRep, hideCtors0 = false) // note ctor
      System.err.println("Compiling tree: "+sru.showCode(tree))
      val r = IntermediateBase.toolBox.eval(tree)
      val applied = (r,csvals) match {
        case (_, Nil) => r
        case (f:(Any=>Any)@unchecked, a0::Nil) => f(a0)
        case (f:((Any,Any)=>Any)@unchecked, a0::a1::Nil) => f(a0,a1)
        case (f:((Any,Any,Any)=>Any)@unchecked, a0::a1::a2::Nil) => f(a0,a1,a2)
        case (f:((Any,Any,Any,Any)=>Any)@unchecked, a0::a1::a2::a3::Nil) => f(a0,a1,a2,a3)
        case (f:((Any,Any,Any,Any,Any)=>Any)@unchecked, a0::a1::a2::a3::a4::Nil) => f(a0,a1,a2,a3,a4)
        case (f:((Any,Any,Any,Any,Any,Any)=>Any)@unchecked, a0::a1::a2::a3::a4::a5::Nil) => f(a0,a1,a2,a3,a4,a5)
        case _ => lastWords(s"unsupported arity (${csvals.size}) for cross-stage compilation of $tree with $csvals")
      }
      applied.asInstanceOf[Typ]
    }
    
    def showScala: String = ibase.showScala(self rep)
    
  }
  
  import quasi.MetaBases.Runtime.ScalaReflectionBaseWithOwnNames
  
  def scalaTreeIn(MBM: MetaBases)(SRB: MBM.ScalaReflectionBase, rep: Rep, extrudedHandle: (BoundVal => MBM.u.Tree) = DefaultExtrudedHandler): MBM.u.Tree = {
    reinterpret(rep, SRB)(extrudedHandle)
  }
  /** For obscure but almost certainly unjustified reasons, Scala complains when calling the above in some contexts. This is a hack to get around it. */
  final def scalaTreeInWTFScala[MBM <: MetaBases](MBM: MBM)(SRB: MBM#ScalaReflectionBase, rep: Rep, extrudedHandle: (BoundVal => MBM#U#Tree) = DefaultExtrudedHandler): MBM#U#Tree =
    scalaTreeIn(MBM)(SRB.asInstanceOf[MBM.ScalaReflectionBase], rep, extrudedHandle.asInstanceOf[BoundVal => MBM.u.Tree])
  
  final def scalaTree(rep: Rep, extrudedHandle: (BoundVal => sru.Tree) = DefaultExtrudedHandler, hideCtors0: Bool = false, markHoles: Bool = false): sru.Tree =
    scalaTreeIn(quasi.MetaBases.Runtime)(new ScalaReflectionBaseWithOwnNames {
      override val hideCtors: Boolean = hideCtors0
      override val markHolesWith_? : Boolean = markHoles
    }, rep, extrudedHandle)
  
  
  def mkVariable[T](r: BoundVal): Variable[T] = Variable.mk[T](r, boundValType(r))
  
}

object IntermediateBase {
  import scala.tools.reflect.ToolBox
  private[squid] lazy val toolBox = sru.runtimeMirror(getClass.getClassLoader).mkToolBox() // Q: necessary 'lazy'? (objects are already lazy)
}
