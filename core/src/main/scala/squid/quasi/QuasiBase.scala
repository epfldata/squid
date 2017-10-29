package squid
package quasi

import squid.ir.RewriteAbort
import squid.ir.Transformer
import utils._
import utils.typing._
import squid.lang.Base
import squid.lang.InspectableBase
import squid.lang.IntermediateBase
import utils.MacroUtils.MacroSetting

import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly
import scala.annotation.unchecked.uncheckedVariance
import scala.collection.mutable


/** Provides the macro infrastructure to allow for using quasiquotes ir"foo" and quasicode ir{foo}, 
  * which are more type-safe interfaces to manipulate code than the Base functions. */
/* TODO implement feature restrictions in quasiquotes, so pattern QQs cannot be defined for non-inspectable bases...
 * Also make Liftable instances nicer since we are now be able to assume QQ/QC can be used on all bases */
trait QuasiBase {
self: Base =>
  
  
  // TODO move these to IntermediateBase
  
  /** Should substitute holes for the given definitions */
  // TODO impl correctly
  //def substitute(r: Rep, defs: Map[String, Rep]): Rep = substituteLazy(r, defs map (kv => kv._1 -> (() => kv._2)))
  //def substituteLazy(r: Rep, defs: Map[String, () => Rep]): Rep
  def substitute(r: => Rep, defs: Map[String, Rep]): Rep
  def substituteLazy(r: => Rep, defs: Map[String, () => Rep]): Rep = substitute(r, defs map (kv => kv._1 -> kv._2()))
  
  /** Not yet used: should eventually be defined by all IRs as something different than hole */
  def freeVar(name: String, typ: TypeRep) = hole(name, typ)
  
  /** Traditional hole with CMTT semantics, in general position; this should extract a `Rep` */
  def hole(name: String, typ: TypeRep): Rep
  
  /** Traditional hole with CMTT semantics, in spliced position (e.g., `$xs` in `ir"List($xs*)"`); this should extract a `Seq[Rep]` */
  def splicedHole(name: String, typ: TypeRep): Rep
  
  /** Higher-Order Pattern (Variable) hole; 
    * this should check that the extracted term does not contain any reference to a bound value contained in the `no` 
    * parameter, and it should extract a function term with the arity of the `yes` parameter. */
  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep
  def hopHole2(name: String, typ: TypeRep, args: List[List[Rep]], visible: List[BoundVal]): Rep = {
    // TODO remove `hopHole` and implement this correctly everywhere
    //val vars = args map (_ map (_.asInstanceOf[BoundVal]))\
    // ^ Note: this will succeed even if there are some non-BoundVal, because BoundVal is eliminated by erasure
    //   it's actually wrong (in AST, readVal(_:BoundVal) adds a Rep wrapper!
    //hopHole(name, typ, vars, visible.toSet -- vars.flatten toList)
    throw new UnsupportedOperationException("Higher-order patterns")
  }
  
  /** Pattern hole in type position */
  def typeHole(name: String): TypeRep
  
  
  
  
  
  
  /* --- --- --- Provided defs --- --- --- */
  
  
  final def substitute(r: => Rep, defs: (String, Rep)*): Rep =
  /* if (defs isEmpty) r else */  // <- This "optimization" is not welcome, as some IRs (ANF) may relie on `substitute` being called for all insertions
    substitute(r, defs.toMap)
  
  protected def mkIR[T,C](r: Rep): IR[T,C] = new IR[T,C] {
    val rep = r
    override def equals(that: Any): Boolean = that match {
      case that: IR[_,_] => rep =~= that.rep
      case _ => false
    }
  }
  
  abstract class Code[+T] protected () extends TypeErased with ContextErased {
    type Typ <: T
    val rep: Rep
    
    def asClosedIR: IR[T,Any] = `internal IR`(rep)
    
    // In the future: have a mehtod that actually checks contexts at runtime, once we have reified hygienic contexts...
    //def asIR[C:Ctx]: Option[IR[T,C]] = ???
    
    def =~= (that: Code[_]): Boolean = rep =~= that.rep
    
    def transformWith(trans: ir.Transformer{val base: self.type}) = Code[T](trans.pipeline(rep))
    
    /** Useful when we have non-denotable types (e.g., extracted types) */
    def withTypeOf[Typ >: T](x: Code[Typ]) = this: Code[Typ]
    
  }
  object Code {
    def apply[T](rep: Rep): Code[T] = mkIR(rep)
    def unapply[T](c: Code[T]): Option[Rep] = Some(c.rep)
  }
  
  object IR {
    def apply[T,C](rep: Rep): IR[T,C] = mkIR(rep)
    def unapply[T,C](ir: IR[T,C]): Option[Rep] = Some(ir.rep)
  }
  
  // Unsealed to allow for abstract constructs to inherit from IR, for convenience.
  abstract class IR[+T, -C] protected () extends Code[T] {
    
    // Note: cannot put this in `IntermediateIROps`, because of the path-dependent type
    def Typ(implicit ev: self.type <:< (self.type with IntermediateBase)): IRType[Typ] = {
      // Ninja path-dependent typing (relies on squid.utils.typing)
      val s: self.type with IntermediateBase = self
      val r: s.Rep = substBounded[Base,self.type,s.type,({type λ[X<:Base] = X#Rep})#λ](rep)
      s.`internal IRType`(s.repType(r))
    }
    
    // type Ctx >: C
    /* ^ this is the 'type-correct' definition: given an x:IR[T,C], we cannot really conclude that the "real" context of
     * x is C, since because of contravariance it *could be* any type less specific than C, such as Any. */
    type Ctx = C @uncheckedVariance
    /* ^ however this definition is much more useful, because we sometimes want to refer to a term's "observed" context 
     * even when it may not be the "real", most specific context.
     * This is safe, because Ctx is a phantom type and so no values will be misinterpreted because of this variance 
     * violation. 
     * An alternative (more cumbersome) solution that does not require @uncheckedVariance is to use type inference, as in:
     *   `def ctxRef[C](x:IR[Any,C]) = new{ type Ctx = C }; val c = ctxRef(x); x : IR[T,c.Ctx]` */ 
    
    val rep: Rep
    
    //// dangerous... -> when Rep extends IR, this makes SchedulingANF consider `x` and `(x:t)` equal, for example, 
    //// which has weird consequences (eg scheduling one as the other):
    //override def equals(that: Any): Boolean = that match {
    //  case that: IR[_,_] => rep =~= that.rep
    //  case _ => false
    //}
    
    def cast[S >: T]: IR[S, C] = this
    def erase: IR[Any, C] = this
    
    override def transformWith(trans: ir.Transformer{val base: self.type}) = IR[T,C](trans.pipeline(rep))
    
    /** Useful when we have non-denotable types (e.g., extracted types) 
      * -- in fact, now that we have `Ctx = C @uncheckedVariance` it's not really useful anymore... */
    override def withTypeOf[Typ >: T](x: Code[Typ]) = this: IR[Typ,C]
    
    /** Useful when we have non-denotable contexts (e.g., rewrite rule contexts) */
    def withContextOf[Ctx <: C](x: IR[Any, Ctx]) = this: IR[T,Ctx]
    //def unsafeWithContextOf[Ctx](x: IR[Any, Ctx]) = this.asInstanceOf[IR[T,Ctx]]  // does not seem to be too useful...
    
    override def toString: String = {
      val repStr = showRep(rep)
      val quote = if ((repStr contains '\n') || (repStr contains '"')) "\"" * 3 else "\""
      s"ir$quote$repStr$quote"
    }
  }
  def `internal IR`[Typ,Ctx](rep: Rep) = IR[Typ,Ctx](rep) // mainly for macros
  type SomeIR = Code[_] // shortcut; avoids showing messy existentials
  
  
  sealed case class IRType[T] private[quasi] (rep: TypeRep) extends TypeErased {
    type Typ = T
    def <:< (that: IRType[_]) = rep <:< that.rep
    def =:= (that: IRType[_]) = rep =:= that.rep
  }
  def `internal IRType`[Typ](trep: TypeRep) = IRType[Typ](trep) // mainly for macros
  
  trait TypeErased { type Typ }
  trait ContextErased { type Ctx }
  
  /** Allows things like TypeOf[ir.type] and TypeOf[irTyp.type], useful when extracted values have non-denotable types  */
  type TypeOf[QT <: TypeErased] = QT#Typ
  
  /** Allows things like ContextOf[ir.type], useful when extracted values have non-denotable contexts  */
  type ContextOf[QT <: ContextErased] = QT#Ctx
  
  
  def irTypeOf[T: IRType] = implicitly[IRType[T]]
  def typeRepOf[T: IRType] = implicitly[IRType[T]].rep
  
  
  val Predef  = new Predef[DefaultQuasiConfig]
  class Predef[QC <: QuasiConfig] {
    val base: self.type = self // macro expansions will make reference to it
    
    type Code[+T] = self.Code[T]
    type IR[+T,-C] = self.IR[T,C]
    type CodeType[T] = self.IRType[T]
    type IRType[T] = self.IRType[T]
    type __* = self.__*
    
    val Const: self.Const.type = self.Const
    def irTypeOf[T: IRType] = self.irTypeOf[T]
    def typeRepOf[T: IRType] = self.typeRepOf[T]
    
    def nullValue[T: IRType](implicit ev: base.type <:< (base.type with IntermediateBase)): IR[T,{}] = {
      val b: base.type with IntermediateBase = ev(base)
      //b.nullValue[T](irTypeOf[T]) // should work, but Scala doesn't like it
      b.nullValue[T](irTypeOf[T].asInstanceOf[b.IRType[T]])
    }
    // Unsafe version:
    //def nullValue[T: IRType]: IR[T,{}] = {
    //  val b = base.asInstanceOf[base.type with IntermediateBase]
    //  b.nullValue[T](irTypeOf[T].asInstanceOf[b.IRType[T]]) }
    
    // Could also use compileTimeOnly here:
    @deprecated("Abort(msg) should only be called from the body of a rewrite rule. " +
      "If you want to abort a rewriting from a function called in the rewrite rule body, " +
      "use `throw RewriteAbort(msg)` instead.", "0.1.1")
    def Abort(msg: String = ""): Nothing = throw new IllegalAccessError("Abort was called outside a rewrite rule!")
    
    object Return {
      private def oops = System.err.println("Return was called outside a rewrite rule!")
      def apply[T,C](x: IR[T,C]): IR[T,C] = {
        oops
        x
      }
      def transforming[A,CA,T,C](a: IR[A,CA])(f: IR[A,CA] => IR[T,C]): IR[T,C] = {
        oops
        f(a)
      }
      def transforming[A,CA,B,CB,T,C](a: IR[A,CA], b: IR[B,CB])(f: (IR[A,CA], IR[B,CB]) => IR[T,C]): IR[T,C] = {
        oops
        f(a,b)
      }
      def transforming[A,CA,B,CB,D,CD,T,C](a: IR[A,CA], b: IR[B,CB], d: IR[D,CD])(f: (IR[A,CA], IR[B,CB], IR[D,CD]) => IR[T,C]): IR[T,C] = {
        oops
        f(a,b,d)
      }
      def transforming[A,CA,T,C](as: List[IR[A,CA]])(f: List[IR[A,CA]] => IR[T,C]): IR[T,C] = {
        oops
        f(as)
      }
      def recursing[T,C](cont: Transformer{val base: self.type} => IR[T,C]): IR[T,C] = {
        oops
        cont(new Transformer { // Dummy transformer that doesn't do anything
          override def transform(rep: base.Rep) = rep
          override val base: self.type with InspectableBase = self.asInstanceOf[self.type with InspectableBase]
        })
      }
    }
    
    import scala.language.dynamics
    object ? extends Dynamic {
      @compileTimeOnly("The `?` syntax can only be used inside quasiquotes and quasicode.")
      def selectDynamic(name: String): Nothing = ???
    }
    
    import scala.language.experimental.macros
    
    implicit class QuasiContext(private val ctx: StringContext) extends self.Quasiquotes.QuasiContext(ctx)
    
    implicit def implicitType[T]: IRType[T] = macro QuasiBlackboxMacros.implicitTypeImpl[QC, T]
    
    object dbg {
      /** import this `implicitType` explicitly to shadow the non-debug one */ 
      @MacroSetting(debug = true) implicit def implicitType[T]: IRType[T] = macro QuasiBlackboxMacros.implicitTypeImpl[QC, T]
    }
    
    implicit def unliftFun[A,B:IRType,C](f: IR[A => B,C]): IR[A,C] => IR[B,C] = a => IR(tryInline(f.rep,a.rep)(typeRepOf[B]))
  }
  
  def `internal abort`(msg: String): Nothing = throw RewriteAbort(msg)
  
  
  
  /** Artifact of a term extraction: map from hole name to terms, types and spliced term lists */
  type Extract = (Map[String, Rep], Map[String, TypeRep], Map[String, Seq[Rep]])
  type Extract_? = Extract |> Option
  protected final val EmptyExtract: Extract = (Map(), Map(), Map())
  protected final val SomeEmptyExtract: Option[Extract] = EmptyExtract |> some
  @inline protected final def mkExtract(rs: String -> Rep *)(ts: String -> TypeRep *)(srs: String -> Seq[Rep] *): Extract = (rs toMap, ts toMap, srs toMap)
  @inline protected final def repExtract(rs: String -> Rep *): Extract = mkExtract(rs: _*)()()
  protected def extractedKeys(e: Extract): Set[String] = e._1.keySet++e._2.keySet++e._3.keySet
  
  protected def mergeOpt(a: Option[Extract], b: => Option[Extract]): Option[Extract] = for { a <- a; b <- b; m <- merge(a,b) } yield m
  protected def merge(a: Extract, b: Extract): Option[Extract] = {
    b._1 foreach { case (name, vb) => (a._1 get name) foreach { va => if (!mergeableReps(va, vb)) return None } }
    b._3 foreach { case (name, vb) => (a._3 get name) foreach { va =>
      if (va.size != vb.size || !(va.iterator zip vb.iterator forall {case (vva,vvb) => mergeableReps(vva, vvb)})) return None } }
    val typs = a._2 ++ b._2.map {
      case (name, t) =>
        a._2 get name map (t2 => name -> mergeTypes(t, t2).getOrElse(return None)) getOrElse (name -> t)
    }
    val splicedVals = a._3 ++ b._3
    val vals = a._1 ++ b._1
    Some(vals, typs, splicedVals)
  }
  protected def mergeAll(as: TraversableOnce[Option[Extract]]): Option[Extract] = {
    if (as isEmpty) return Some(EmptyExtract)
    
    //as.reduce[Option[Extract]] { case (acc, a) => for (acc <- acc; a <- a; m <- merge(acc, a)) yield m }
    /* ^ not good as it evaluates all elements of `as` (even if it's an Iterator or Stream) */
    
    val ite = as.toIterator
    var res = ite.next()
    while(ite.hasNext && res.isDefined) res = mergeOpt(res, ite.next())
    res
  }
  
  def mergeableReps(a: Rep, b: Rep): Boolean = a =~= b
  
  def mergeTypes(a: TypeRep, b: TypeRep): Option[TypeRep] =
    // Note: We can probably do better than =:=, but that is up to the implementation of TypingBase to override it
    if (typEq(a,b)) Some(a) else None
  
  
  private var extracting = false
  protected def isExtracting = extracting
  final protected def isConstructing = !isExtracting
  def wrapConstruct(r: => Rep) = { val old = extracting; extracting = false; try r finally { extracting = old } }
  def wrapExtract  (r: => Rep) = { val old = extracting; extracting = true;  try r finally { extracting = old } }
  //def wrapExtract  (r: => Rep) = { val old = extracting; extracting = true; println("BEG EXTR"); try r finally { println("END EXTR"); extracting = old } }
  // ^ TODO find a solution cf by-name params, which creates owner corruption in macros

  
  type __* = Seq[IR[_,_]] // used in insertion holes, as in:  ${xs: __*}
  
  
  
  /** TODO make it more generic: use Liftable! */
  /* To support insertion syntax `$xs` (in ction) or `$$xs` (in xtion) */
  def $[T,C](q: IR[T,C]*): T = ??? // TODO B/E  -- also, rename to 'unquote'?
  //def $[T,C](q: IR[T,C]): T = ??? // Actually unnecessary
  def $[A,B,C](q: IR[A,C] => IR[B,C]): A => B = ??? // TODO rely on implicit liftFun instead?
  
  def $Code[T](q: Code[T]): T = ??? // TODO B/E  -- also, rename to 'unquote'?
  def $Code[A,B](q: Code[A] => Code[B]): A => B = ???
  
  /* To support hole syntax `?xs` (old syntax `$$xs`) (in ction) or `$xs` (in xtion)  */
  def $$[T](name: Symbol): T = ???
  /* To support hole syntax `$$xs: _*` (in ction) or `$xs: _*` (in xtion)  */
  def $$_*[T](name: Symbol): Seq[T] = ???
  
  /** Higher-order pattern */
  def $$_hop[T](name: Symbol)(args: Any*): T = ???
  
  
  implicit def liftFun[A:IRType,B,C](qf: IR[A,C] => IR[B,C]): IR[A => B,C] = {
    val bv = bindVal("lifted", typeRepOf[A], Nil) // add TODO annotation recording the lifting?
    val body = qf(IR(bv |> readVal)).rep
    IR(lambda(bv::Nil, body))
  }
  implicit def liftCodeFun[A:IRType,B](qf: Code[A] => Code[B]): Code[A => B] = {
    val bv = bindVal("lifted", typeRepOf[A], Nil) // add TODO annotation recording the lifting?
    val body = qf(Code(bv |> readVal)).rep
    Code(lambda(bv::Nil, body))
  }
  implicit def unliftFun[A,B:IRType,C](qf: IR[A => B,C]): IR[A,C] => IR[B,C] = x => {
    IR(app(qf.rep, x.rep)(typeRepOf[B]))
  }
  implicit def unliftCodeFun[A,B:IRType](qf: Code[A => B]): Code[A] => Code[B] = x => {
    Code(app(qf.rep, x.rep)(typeRepOf[B]))
  }
  
  import scala.language.experimental.macros
  
  class Quasiquotes[QC <: QuasiConfig] {
    val base: QuasiBase.this.type = QuasiBase.this
    
    implicit class QuasiContext(private val ctx: StringContext) {
      
      object ir { // TODO try to refine the types..?
        //def apply(inserted: Any*): Any = macro QuasiMacros.applyImpl[QC]
        //def unapply(scrutinee: Any): Any = macro QuasiMacros.unapplyImpl[QC]
        // ^ versions above give less hints to macro-blind IDEs, but may be faster to compile 
        // as they involve an easier (trivial) subtype check: macro_result.tpe <: Any (performed by scalac)
        def apply(inserted: Any*): SomeIR = macro QuasiMacros.applyImpl[QC]
        def unapply(scrutinee: SomeIR): Any = macro QuasiMacros.unapplyImpl[QC]
      }
      
      object dbg_ir { // TODO try to refine the types..?
        @MacroSetting(debug = true) def apply(inserted: Any*): Any = macro QuasiMacros.applyImpl[QC]
        @MacroSetting(debug = true) def unapply(scrutinee: Any): Any = macro QuasiMacros.unapplyImpl[QC]
      }
      
      object code {
        def apply(inserted: Any*): SomeIR = macro QuasiMacros.applyImpl[QC]
        def unapply(scrutinee: SomeIR): Any = macro QuasiMacros.unapplyImpl[QC]
      }
      object c {
        def apply(inserted: Any*): SomeIR = macro QuasiMacros.applyImpl[QC]
        def unapply(scrutinee: SomeIR): Any = macro QuasiMacros.unapplyImpl[QC]
      }
      
    }
    
  }
  class Quasicodes[QC <: QuasiConfig] {
    val qcbase: QuasiBase.this.type = QuasiBase.this // macro expansions will make reference to it
    
    def ir[T](tree: T): IR[T, _] = macro QuasiMacros.quasicodeImpl[QC]
    @MacroSetting(debug = true) def dbg_ir[T](tree: T): IR[T, _] = macro QuasiMacros.quasicodeImpl[QC]
    
    def code[T](tree: T): IR[T, _] = macro QuasiMacros.quasicodeImpl[QC]
    @MacroSetting(debug = true) def dbg_code[T](tree: T): IR[T, _] = macro QuasiMacros.quasicodeImpl[QC]
    
    def $[T,C](q: IR[T,C]*): T = macro QuasiMacros.forward$ // to conserve the same method receiver as for QQ (the real `Base`)
    def $[A,B,C](q: IR[A,C] => IR[B,C]): A => B = macro QuasiMacros.forward$2
    //def $[T,C](q: IR[T,C]): T = macro QuasiMacros.forward$ // Actually unnecessary
    //def $[T,C](q: IR[T,C]*): T = macro QuasiMacros.forwardVararg$ // Actually unnecessary
    def $$[T](name: Symbol): T = macro QuasiMacros.forward$$
    
    type $[QT <: TypeErased] = TypeOf[QT]
    
  }
  object Quasicodes extends Quasicodes[DefaultQuasiConfig]
  object Quasiquotes extends Quasiquotes[DefaultQuasiConfig]
  
  // Note: could optimize cases with no key (currently encoded usign Unit) -- pur in a `mutable.HashMap[String,Rep]()`
  private val caches = mutable.HashMap[String,mutable.HashMap[Any,Rep]]()
  def cacheRep[K](id: String, key: K, mk: K => Rep): Rep = {
    caches.getOrElseUpdate(id,mutable.HashMap[Any,Rep]()).getOrElseUpdate(key,mk(key))
    //mk(key)  // toggle comment to see the effect of NOT caching
  }
  
}

object QuasiBase {
  
  /** Used to tag (the upper bound of) types generated for type holes, 
    * and to have a self-documenting name when the type is widened because of scope extrusion.
    * Note: now that extracted type symbols are not generated from a local `trait` but instead from the `Typ` member of a local `object`, 
    *   scope extrusion does not neatly widen extruded types to just `<extruded type>` anymore, but often things like:
    *   `Embedding.IRType[MyClass.s.Typ]]`.
    *   Still, this trait is useful as it is used in, e.g., `QuasiTypeEmbedded` to customize the error on implicit 
    *   type not found. It's also the inferred type for things like `case List($a:$ta,$b:$tb)`, which prompts 
    *   a QQ error -- this is not really necessary, just a nicety. 
    *   Eventually we can totally get rid of that bound, as QuasiEmbedder now internally relies on `Extracted` instead. */
  type `<extruded type>`
  
}

/** Annotation used on extracted types */
class Extracted extends StaticAnnotation

object SuppressWarning {
  implicit object `scrutinee type mismatch`
}




