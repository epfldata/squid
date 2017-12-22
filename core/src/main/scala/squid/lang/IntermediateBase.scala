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
  
  val DefaultExtrudedHandler = (bv: BoundVal) => throw ir.IRException(s"Extruded bound variable cannot be reinterpreted: $bv")
  
  def reinterpret(r: Rep, newBase: Base)(extrudedHandle: (BoundVal => newBase.Rep) = DefaultExtrudedHandler): newBase.Rep
  
  def nullValue[T: CodeType]: Code[T,{}]
  
  
  //override def showRep(r: Rep) = showScala(r)
  @volatile private var showing = false
  protected def isShowing = showing
  override def showRep(r: Rep) = synchronized { if (showing) super.showRep(r) else try { showing = true; showScala(r) } finally { showing = false } }
  def showScala(r: Rep) = sru.showCode( scalaTree(r, bv => sru.Ident(sru.TermName(boundValUniqueName(bv))), markHoles = true) )
  // ^ Note: used to show extruded vals as s"?${bv}?" which looked ugly (as in `?[x:Int]?`)
  
  def boundValUniqueName(bv: BoundVal): String
  
  def extractVal(r: Rep): Option[BoundVal]
  
  
  implicit class IntermediateRepOps(private val self: Rep) {
    def typ = repType(self)
  }
  
  implicit class IntermediateCodeOps[Typ,Ctx](private val self: Code[Typ,Ctx]) {
    /* Note: making it `def typ: CodeType[Typ]` woule probably be unsound! */
    def typ: CodeType[_ <: Typ] = `internal CodeType`(trep)
    def trep = repType(self.rep)
    
    import scala.language.experimental.macros
    def subs[T1,C1](s: => (Symbol, Code[T1,C1])): Code[Typ,_ >: Ctx] = macro quasi.QuasiMacros.subsImpl[T1,C1]
    @MacroSetting(debug = true) def dbg_subs[T1,C1](s: => (Symbol, Code[T1,C1])): Code[Typ,_ >: Ctx] = macro quasi.QuasiMacros.subsImpl[T1,C1]
    
    def reinterpretIn(newBase: Base): newBase.Code[Typ,Ctx] =
      newBase.`internal Code`(newBase.wrapConstruct( reinterpret(self.rep, newBase)(DefaultExtrudedHandler) ))
    
    /** Executes the code at runtime using Java reflection */
    def run(implicit ev: {} <:< Ctx): Typ = {
      val Inter = new ir.BaseInterpreter
      reinterpret(self.rep, Inter)().asInstanceOf[Typ]
    }
    
    /** Compiles and executes the code at runtime using the Scala ToolBox compiler */
    def compile(implicit ev: {} <:< Ctx): Typ = {
      // TODO make `compile` a macro that can capture surrounding vars!!
      val s = scalaTree(self.rep,hideCtors0 = false) // note ctor
      System.err.println("Compiling tree: "+sru.showCode(s))
      IntermediateBase.toolBox.eval(s).asInstanceOf[Typ]
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
  
  
  def mkVariable[T](r: BoundVal): Variable[T] =
    // Note: the reason we make the class hierarchy so awkward is so users can write `new Vairable[Int]("someName")`
    new Variable[T]()(CodeType(boundValType(r))) { override protected val bound = r }
  
}

object IntermediateBase {
  import scala.tools.reflect.ToolBox
  private lazy val toolBox = sru.runtimeMirror(getClass.getClassLoader).mkToolBox() // Q: necessary 'lazy'? (objects are already lazy)
}
