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

package squid.lang

import squid.quasi


/** The base trait defining, in the tagless final style, the core language of Squid:
  *   constants, lambdas, method applications, object creations and module references. */
trait Base extends TypingBase with quasi.QuasiBase {
  
  /** Internal, untype representation of code */
  type Rep
  
  /** Representation of bound values or "symbols" */
  type BoundVal
  
  /** Bound value annotation */
  type Annot = (TypeRep, List[ArgList])
  
  /** Creates a new value with the specified type */
  def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal
  
  /** Returns an internal code representation (Rep) corresponding to a value read/access */
  def readVal(v: BoundVal): Rep
  
  /** Scala constant, including base numeric types, Unit, String, and Class */
  def const(value: Any): Rep // Note: not taking a sru.Constant as argument, because `const` also receives things like () -- Unit "literal"
  
  /** Lambda expression with variable number of parameters  */
  def lambda(params: List[BoundVal], body: => Rep): Rep
  
  /** Module (`object`) reference that can be accessed statically, such as `scala.Option` */
  def staticModule(fullName: String): Rep
  
  /** Module (`object`) reference based on some non-static prefix, such as `(new MyTrait).MyObject` */
  def module(prefix: Rep, name: String, typ: TypeRep): Rep
  
  /** Object creation; the parameters provided to the constructor in a full object creation are passed via a methodApp */
  def newObject(tp: TypeRep): Rep
  
  /** Scala method application, with a receiver, method identifier, type arguments, list of argument lists, and return type */
  def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep
  
  /** Wraps code that is passed as a by-name argument to a method (such as the branhces of an IfThenElse) */
  def byName(arg: => Rep): Rep
  
  /** Method identifier */
  type MtdSymbol <: AnyRef  // AnyRef bound so it can be used in squid.utils.Lazy (see the @mirror/@embed annotations)
  
  /** Parameter `static` should be true only for truly static methods (in the Java sense)
    * Note: index should be None when the symbol is not overloaded, to allow for more efficient caching */
  def loadMtdSymbol(typ: TypSymbol, symName: String, index: Option[Int] = None, static: Boolean = false): MtdSymbol
  
  /** High-level interface whose implementations should specify how to construct (and potentially also deconstruct) constants */
  trait ConstAPI {
    def apply[T: CodeType](v: T): Code[T,Any] = `internal Code`(const(v))
  }
  val Const: ConstAPI
  
  /** High-level interface which implementation should specify how to construct (and potentially also deconstruct) constants */
  def repEq(a: Rep, b: Rep): Boolean
  
  
  // Method with a default implementation:
  
  
  /** Specifies how to display an internal representation */
  def showRep(r: Rep) = r.toString
  
  /** Function1 application */
  def app(fun: Rep, arg: Rep)(retTp: TypeRep): Rep = methodApp(fun, Function1ApplySymbol, Nil, Args(arg)::Nil, retTp)
  
  // TODO don't define here; force bases to implement explicitly
  /** Override to allow Squid to inline things in places like inserted automatically-lifted functions 
    * (e.g., {{{code"(x:Int) => ${(x:Code[Int]) => code"$x+1"}(x)"}}}) */
  def tryInline(fun: Rep, arg: Rep)(retTp: TypeRep): Rep = app(fun,arg)(retTp)
  
  /** Let-binding of a value */
  def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = {
    app(lambda(bound::Nil, body), value)(bodyType)
  }
  
  /** Override to give special meaning to type ascription */
  def ascribe(self: Rep, typ: TypeRep): Rep = self
  
  
  // Helpers:
  
  
  implicit class RepOps(private val self: Rep) {
    def =~= (that: Rep) = repEq(self, that)
    
    /** Useful for inspection with quasiquotes; the Nothing context prevents it from being used as is (which would be unsafe). */
    def asCode = `internal Code`[Any,Nothing](self)
    
    def show = showRep(self)
  }
  
  
  /** Just a shortcut for methodApp */
  final def mapp(self: Rep, mtd: MtdSymbol, tp: TypeRep)(targs: TypeRep*)(argss: ArgList*): Rep =
    methodApp(self, mtd, targs.toList, argss.toList, tp)
  
  
  // TODO move all these into a Builtin object and remove `lazy`; or better: use @embed to create a core set of required features
  protected lazy val Function1ApplySymbol = loadMtdSymbol(loadTypSymbol("scala.Function1"), "apply")
  protected lazy val squidLib = staticModule("squid.lib.package")
  protected lazy val squidLibSym = loadTypSymbol("squid.lib.package$")
  protected lazy val BooleanType = staticTypeApp(loadTypSymbol("scala.Boolean"),Nil)
  protected lazy val BooleanAndSymbol = loadMtdSymbol(squidLibSym, "And")
  protected lazy val BooleanOrSymbol = loadMtdSymbol(squidLibSym, "Or")
  def and(lhs: Rep, rhs: => Rep) = methodApp(squidLib,BooleanAndSymbol,Nil,Args(lhs,rhs)::Nil,BooleanType)
  def or(lhs: Rep, rhs: => Rep) = methodApp(squidLib,BooleanOrSymbol,Nil,Args(lhs,rhs)::Nil,BooleanType)
  
  
  /** Argument lists can either be:
    *  - `Args(xs...)` a basic argument list to a method with no varargs; eg in `Math.pow(.5,2)`
    *  - `ArgsVarargs(Args(xs...),Args(ys...))` an argument list followed by arguments to a vararg parameter; eg in `List(1,2,3)`
    *  - `ArgsVarargSpliced(Args(xs...),y)` an argument list followed by a spliced argument to a vararg parameter; eg in `List(xs:_*)` */
  sealed trait ArgList extends Product with Serializable {
    def repsIt: Iterator[Rep] = reps.iterator
    def reps: Seq[Rep]
    override def toString = show(_ toString)
    def show(rec: Rep => String, forceParens: Boolean = true) = {
      val strs = this match {
        case Args(as @ _*) => as map rec
        case ArgsVarargs(as, vas) => as.reps ++ vas.reps map rec
        case ArgsVarargSpliced(as, va) => as.reps.map(rec) :+ s"${rec(va)}: _*"
      }
      if (forceParens || strs.size != 1) strs mkString ("(",",",")") else strs mkString ","
    }
    def map(b: Base)(f: Rep => b.Rep): b.ArgList
  }
  case class Args(reps: Rep*) extends ArgList {
    def apply(vreps: Rep*) = ArgsVarargs(this, Args(vreps: _*))
    def splice(vrep: Rep) = ArgsVarargSpliced(this, vrep)
    def map(b: Base)(f: Rep => b.Rep): b.Args = b.Args(reps map f: _*)
  }
  object ArgList {
    def unapplySeq(x: ArgList) = x match {
      case Args(as @ _*) => Some(as)
      case ArgsVarargs(as, vas) => Some(as.reps ++ vas.reps)
      case ArgsVarargSpliced(_, _) => None
    }
  }
  case class ArgsVarargs(args: Args, varargs: Args) extends ArgList {
    val reps = args.reps ++ varargs.reps
    def map(b: Base)(f: Rep => b.Rep): b.ArgsVarargs = b.ArgsVarargs(args.map(b)(f), varargs.map(b)(f))
  }
  case class ArgsVarargSpliced(args: Args, vararg: Rep) extends ArgList {
    val reps = args.reps :+ vararg
    def map(b: Base)(f: Rep => b.Rep): b.ArgsVarargSpliced = b.ArgsVarargSpliced(args.map(b)(f), f(vararg))
  }
  
  
  /** `EmbeddedType` is used to store static references to type symbols and associated method symbols, so that 
    * when the right type is present, quasiquotes can generate direct field accesses instead of calls to `loadTypeSymbol`
    * and `loadMethodSymbol` (which have to go through hash-table lookups to find the right symbols). */
  class EmbeddedType(val tsym: TypSymbol) {
    val asStaticallyAppliedType = squid.utils.Lazy(staticTypeApp(tsym, Nil))
  }
  
  
  abstract class SymbolLoadingException(cause: Exception) extends Exception(cause)
  case class MtdSymbolLoadingException(typ: TypSymbol, symName: String, index: Option[Int], cause: Exception) extends SymbolLoadingException(cause)
  case class TypSymbolLoadingException(fullName: String, cause: Exception) extends SymbolLoadingException(cause)
  
  
}
