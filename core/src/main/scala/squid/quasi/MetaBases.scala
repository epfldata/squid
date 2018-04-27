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
package quasi

import utils._
import squid.utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.sru
import squid.lang.Base

trait MetaBases {
  type U = u.type
  val u: scala.reflect.api.Universe
  import u._
  
  object Helpers extends {val uni: u.type = u} with meta.UniverseHelpers[u.type]
  import Helpers.TreeOps
  
  def freshName(hint: String): TermName
  def curatedFreshName(hint: String): TermName =
    //freshName(hint replace('$', '_'))
    freshName(hint replace('$', '_') replace('<', '_') replace('>', '_'))
  
  /** Base that generates the Scala code necessary to construct the object program.
    * This class let-binds type symbols, method symbols, type applications and modules: the corresponding definitions
    * are stored in the `symbols` mutable buffer.
    * Note: these are let-bound but not cached – caching is assumed to be performed by the caller (eg: ModularEmbedding).
    * @param baseType if defined, will be used to find potential static field accesses to the type/method symbols */
  class MirrorBase(val Base: Tree, baseType: Option[Type] = None) extends Base {
    /* TODO: more clever let-binding so defs used once won't be bound? -- that would require changing `type Rep = Tree` to something like `type Rep = () => Tree` */
    import scala.collection.mutable
    
    /** For legibility of the gen'd code, calls `mapp` instead of `methodApp`.
      * Note: maybe it will make the gen'd pgrm slower (cf: more Seq/List ction?) */
    //val shortAppSyntax = true
    val shortAppSyntax = false
    
    val symbols = mutable.Buffer[(TermName, Tree)]()
    def mkSymbolDefs = symbols map { case(n, t) => q"val $n = $t" }
    
    
    type Rep = Tree
    
    /** BoundVal can be a new symbol to be instantiated by the MirrorBase code generator, or a reference to a
      * pre-existing symbol instantiated somewhere else. This became important with the support for first-class variable symbols. */
    sealed trait BoundVal { def tree: Tree }
    case class Existing(tree: Tree) extends BoundVal
    case class New(originalName: String, valName/*(in gen'd code)*/: TermName, typRep: TypeRep, annots: List[Annot]) extends BoundVal {
      def tree = Ident(valName)
    }
    
    type TypeRep = Tree
    
    type MtdSymbol = Tree
    type TypSymbol = (String, Tree) // (nameHint, exprTree)
    
    
    def repEq(a: Rep, b: Rep): Boolean = a == b
    def typLeq(a: TypeRep, b: TypeRep): Boolean = ???
    
    
    def loadTypSymbol(fullName: String): TypSymbol = {
      val nameHint = fullName.drop(fullName.lastIndexOf('.')+1)
      val n = curatedFreshName(nameHint+"Sym")
      val encodedName = TermName(fullName).encodedName.toTermName
      nameHint -> baseType.map(_.member(encodedName)).filter(_ =/= NoSymbol).fold[Tree] {
        // TODO warn if some OpenWorld trait is not mixed in and the symbol is not found?
        val s = q"$Base.loadTypSymbol($fullName)"
        symbols += n -> s
        q"$n"
      } { sym =>
        val s = q"$Base.$encodedName"
        symbols += n -> s
        q"$n.tsym"
      }
    }
    
    def loadMtdSymbol(typ: TypSymbol, symName: String, index: Option[Int], static: Boolean = false): MtdSymbol = {
      val n = curatedFreshName(symName)
      val s = typ._2 match {
        case q"$n.tsym" => // TODO better error if sym not found? – or even fallback on dynamic loading
          q"$n.${TermName(s"method $symName${index.fold("")(":"+_)}${if (static) ":" else ""}").encodedName.toTermName}.value"
        case n => q"$Base.loadMtdSymbol($n, $symName, $index, $static)"
      }
      symbols += n -> s
      q"$n"
    }
    
    def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal =
      //TermName(name) -> typ // We assume it's fine without a fresh name, since the binding structure should reflect that of the encoded program
      New(name, TermName("_$"+name), typ, annots) // Assumption: nobody else uses names of this form... (?)
    
    def readVal(v: BoundVal): Rep = q"$Base.readVal(${v.tree})"
    
    def const(value: Any): Rep = q"$Base.const(${Constant(value)})"
    
    def annot(a: Annot) = q"${a._1} -> ${mkNeatList(a._2 map argList)}"
    
    def lambda(params: List[BoundVal], body: => Rep): Rep = q"""
      ..${params collect { case New(on, vn, vt, anns) => q"val $vn = $Base.bindVal($on, $vt, ${mkNeatList(anns map annot)})" }}
      $Base.lambda(${mkNeatList(params map (_.tree))}, $body)
    """
    
    override def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = q"""
      ..${bound |> {
        case Existing(_) => q""
        case New(_1,_2,_3,_4) => q"val ${_2} = $Base.bindVal(${_1}, ${_3}, ${mkNeatList(_4 map annot)})"
      }}
      $Base.letin(${bound.tree}, $value, $body, $bodyType)
    """
    
    override def tryInline(fun: Rep, arg: Rep)(retTp: TypeRep): Rep =
      q"$Base.tryInline($fun, $arg)($retTp)"
    
    def newObject(tp: TypeRep): Rep = q"$Base.newObject($tp)"
    
    def moduleObject(fullName: String, isPackage: Boolean): Rep = {
      val n = curatedFreshName(fullName.drop(fullName.lastIndexOf('.')+1))
      symbols += n -> q"$Base.moduleObject($fullName, $isPackage)"
      q"$n"
    }
    def staticModule(fullName: String): Rep = {
      val n = curatedFreshName(fullName.drop(fullName.lastIndexOf('.')+1))
      symbols += n -> q"$Base.staticModule($fullName)"
      q"$n"
    }
    def module(prefix: Rep, name: String, typ: TypeRep): Rep = q"$Base.module($prefix, $name, $typ)"
    
    
    def argList(argl: ArgList): Tree = argl match {
      case Args(reps @ _*) => q"$Base.Args(..$reps)"
      case ArgsVarargs(args, varargs) => q"$Base.ArgsVarargs(${argList(args)}, ${argList(varargs)})"
      case ArgsVarargSpliced(args, vararg) => q"$Base.ArgsVarargSpliced(${argList(args)}, $vararg)"
    }
    
    def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = {
      val as = argss map argList
      if (shortAppSyntax) q"$Base.mapp($self, $mtd, $tp)(..$targs)(..$as)"
      else q"$Base.methodApp($self, $mtd, ${mkNeatList(targs)}, ${mkNeatList(as)}, $tp)"
    }
    
    def byName(arg: => Rep) = q"$Base.byName($arg)"
    
    
    //def uninterpretedType[A: sru.TypeTag]: TypeRep = q"$Base.uninterpretedType[${typeOf[A]}]"
    def uninterpretedType[A: sru.TypeTag]: TypeRep = { // Type tags can be very hairy, so we let-bind them
      val n = curatedFreshName(typeOf[A].typeSymbol.name.toString)
      symbols += n -> q"$Base.uninterpretedType[${typeOf[A]}]"
      q"$n"
    }
    
    
    def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
      val n = curatedFreshName(typ._1)
      symbols += n -> q"$Base.typeApp($self, ${typ._2}, ${mkNeatList(targs)})"
      q"$n"
    }
    def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
      val n = curatedFreshName(typ._1)
      val s = typ._2 match {
        // As an optimization, if the type is applied to no type argument, access the `asStaticallyAppliedType` field:
        case q"$n.tsym" if targs.isEmpty => q"$n.asStaticallyAppliedType.value"
        case n => q"$Base.staticTypeApp(${typ._2}, ${mkNeatList(targs)})"
      }
      symbols += n -> s
      q"$n"
    }
    
    def recordType(fields: List[(String, TypeRep)]): TypeRep = ???
    
    def constType(value: Any, underlying: TypeRep): TypeRep = q"$Base.constType(${Constant(value)}, $underlying)"
    
    
    
    
    def mkNeatList(xs: Seq[Tree]) = xs match {
      case Seq() => q"scala.Nil"
      case _ => q"scala.List(..$xs)"
    }
    
    
    
    def hole(name: String, typ: TypeRep): Rep = q"$Base.hole($name, $typ)"
    def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep =
      q"$Base.hopHole($name, $typ, ${yes map (_ map (_.tree))}, ${no map (_.tree)})"
    def splicedHole(name: String, typ: TypeRep): Rep = q"$Base.splicedHole($name, $typ)"
    
    def substitute(r: => Rep, defs: Map[String, Rep]): Rep =
    //if (defs isEmpty) r else  // <- This "optimization" is not welcome, as some IRs (ANF) may relie on `substitute` being called for all insertions
      q"$Base.substitute($r, ..${defs map {case (name, rep) => q"$name -> $rep"}})"
    /* 
    /** Note: We could implement the method above by actually doing substitution in the Scala tree as below,
      * but that would break the semantics of `MirrorBase`, which is really to forward operations instead of applying
      * them eagerly. So we generate actual substitution code instead. */
    def substitute(r: Rep, defs: Map[String, Rep]): Rep = r transform {
      case h @ q"$Base.hole(${Literal(Constant(name: String))}, $typ)" =>
        defs.getOrElse(name, h)
    }
    */
    
    def typeHole(name: String): TypeRep = q"$Base.typeHole($name)"
    
    
    override def ascribe(self: Rep, typ: TypeRep): Rep = q"$Base.ascribe($self, $typ)"
    
    object Const extends ConstAPI {
      def unapply[T: sru.TypeTag](ir: Code[T,_]): Option[T] = ir match {
        case q"$b.const[$typ](${Literal(Constant(value))})" if sru.typeOf[T] <:< typ.tpe.asInstanceOf[sru.Type] => // TODO check base?
          Some(value.asInstanceOf[T])
        case _ => None
      }
    }
    
  }
  
  
  
  
  
  /** Base that simply outputs the Scala tree representation of the DSL program.
    * It does not add types to the trees, although it could (to some extent). */
  class ScalaReflectionBase extends Base {
    
    //val ascribeValBindings = true
    val ascribeValBindings = false
    
    //val hideCtors = true
    val hideCtors = false // showCode hides them anyways!
    
    val startPathsFromRoot = false
    
    val markHolesWith_? = false
    
    type Rep = Tree
    type BoundVal = (TermName, TypeRep)
    type TypeRep = Tree
    
    type MtdSymbol = TermName
    type TypSymbol = () => sru.TypeSymbol // to delay computation, since we won't need most of them! (only needed in typeApp)
    
    
    def repEq(a: Rep, b: Rep): Boolean = a == b
    def typLeq(a: TypeRep, b: TypeRep): Boolean = ???
    
    
    def freshName(hint: String): TermName = MetaBases.this.freshName(hint)
    
    
    def loadTypSymbol(fullName: String): TypSymbol = () => ir.RuntimeSymbols.loadTypSymbol(fullName)
    
    def loadMtdSymbol(typ: TypSymbol, symName: String, index: Option[Int], static: Boolean = false): MtdSymbol =
      TermName(symName)
    
    def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal =
      //TermName(name) -> typ  // [wrong] Assumption: it will be fine to use the unaltered name here
      freshName(name toString) -> typ  // We need fresh names to avoid wrong capture; eg: when introducing a new parameter name in the middle of a program
    //def bindVal(name: String, typ: TypeRep): BoundVal = TermName("_$"+name) -> typ
    
    def readVal(v: BoundVal): Rep = q"${v._1}"
    def const(value: Any): Rep = value match {
      case cls: Class[_] => q"_root_.scala.Predef.classOf[${ruh.srum.classSymbol(cls).asInstanceOf[u.Symbol]}]" // FIXME
      case _ => Literal(Constant(value))
    }
    def lambda(params: List[BoundVal], body: => Rep): Rep = q"""
      (..${params map { case (vn, vt) => q"val $vn: $vt" }}) => $body
    """
    
    override def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = q"""
      val ${bound._1}: ${if (ascribeValBindings) bound._2 else tq""} = $value
      ..$body
    """
      //val ${bound._1}: ${if (ascribeValBindings) bound._2 else EmptyTree} = $value  // mks errors like Error:(65, 21) value + is not a member of <notype>
    
    override def and(lhs: Rep, rhs: => Rep): Rep = q"$lhs && $rhs"
    override def or(lhs: Rep, rhs: => Rep): Rep = q"$lhs || $rhs"
    
    def newObject(tp: TypeRep): Rep = New(tp)
    def moduleObject(fullName: String, isPackage: Boolean): Rep = {
      val path = fullName.splitSane('.').toList
      path.tail.foldLeft(q"${TermName(path.head)}":Tree)((acc,n) => q"$acc.${TermName(n)}")
    }
    def staticModule(fullName: String): Rep = {
      val path = fullName.splitSane('.').toList
      path.tail.foldLeft(q"${TermName(path.head)}":Tree)((acc,n) => q"$acc.${TermName(n)}")
    }
    def module(prefix: Rep, name: String, typ: TypeRep): Rep = q"$prefix.${TermName(name)}"
    def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = {
      val pref = if (hideCtors && mtd == termNames.CONSTRUCTOR) q"$self" else q"$self.$mtd"
      q"$pref[..$targs](...${
        def quote(argl: ArgList): Seq[Tree] = argl match {
          case Args(reps @ _*) => reps
          case ArgsVarargs(args, varargs) => quote(args) ++ quote(varargs)
          case ArgsVarargSpliced(args, vararg) => quote(args) :+ q"$vararg: _*"
        }
        argss map quote})" // Note: could also call  internal.setType ...?
    }
    
    def byName(arg: => Rep): Rep = arg
    
    def uninterpretedType[A: sru.TypeTag]: TypeRep = tq"${typeOf[A]}"
    
    def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
      val tp = typ()
      val pre = self match {
        // sometimes `staticTypeApp` produces such trees, and it really corresponds to a type projection:
        case tq"$t.${tn:TypeName}" =>
          return tq"$t.$tn#${TypeName(tp.name.toString)}"
        case tq"$t.type" => t
        case _ => self
      }
      if (tp.isModuleClass) {
        assert(targs.isEmpty, s"Non-empty targs $targs")
        tq"$pre.${TermName(tp.name.toString)}.type"
      }
      else tq"$pre.${TypeName(tp.name.toString)}[..$targs]"
    }
    def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
      val tp = typ()
      var nameChain = ((Iterator iterate tp.owner)(_.owner) takeWhile (s => s.name.toString != "<root>")
        map (s => TermName(s.name.toString)) foldLeft List.empty[TermName]) (_.::(_))
      if (startPathsFromRoot) nameChain ::= TermName("_root_")
      val path = nameChain.tail.foldLeft(Ident(nameChain.head):Tree){ (p, n) => q"$p.$n" }
      typeApp(path, () => tp, targs)
    }
    
    def recordType(fields: List[(String, TypeRep)]): TypeRep = ??? // TODO rm
    
    def repType(r: Rep): TypeRep = ??? // TODO impl (store types using internal)
    
    
    /* Note about hygiene: typically when using ScalaReflectionBase, we already ensure that there are no free variables
     * lying around (cf. implicit evidence in method `compile`); the other main use case is pretty-printing, where
     * `markHolesWith_?` will typically be turned on so we can clearly identify free variables. */
    private def holeName(name: String) = 
      if (markHolesWith_?) "?"+name else name
    def hole(name: String, typ: TypeRep): Rep = 
      q"${TermName(name |> holeName)}"
    def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep = 
      q"${TermName(name |> holeName)}"
    def splicedHole(name: String, typ: TypeRep): Rep = 
      q"${TermName(name |> holeName)}: _*"
    
    def substitute(r: => Rep, defs: Map[String, Rep]): Rep = r transform {
      //case h @ q"${TermName(name)}" =>  // Weird! this does not seem to match...
      case h @ Ident(TermName(name)) =>
        defs.getOrElse(name, h)
    }
    
    def typeHole(name: String): TypeRep = tq"${TypeName(name)}"
    
    def constType(value: Any, underlying: TypeRep): TypeRep = tq"$underlying"
    
    
    
    override def ascribe(self: Rep, typ: TypeRep): Rep = q"$self: $typ"
    
    object Const extends ConstAPI {
      def unapply[T: sru.TypeTag](ir: Code[T,_]): Option[T] = ir match {
        case Literal(Constant(v)) => Some(v.asInstanceOf[T]) // TODO check type?
        case _ => None
      }
    }
    
    
  }
}

object MetaBases {
  
  object Runtime extends MetaBases {
    val u: sru.type = sru
    
    private var varCount = 0
    def freshName(hint: String) = sru.TermName(hint+s"_$varCount") alsoDo (varCount += 1)
    
    class ScalaReflectionBaseWithOwnNames extends Runtime.ScalaReflectionBase {
      private var varCount = 0
      override def freshName(hint: String): sru.TermName = sru.TermName(hint+s"_$varCount") alsoDo (varCount += 1)
    }
    object ScalaReflectionBase extends ScalaReflectionBaseWithOwnNames
    
  }
  
}










