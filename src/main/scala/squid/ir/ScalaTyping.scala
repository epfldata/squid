package squid
package ir

import utils._
import CollectionUtils.TraversableOnceHelper
import utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.{srum, sru}
import squid.lang.Base
import squid.lang.IntermediateBase
import squid.quasi.ModularEmbedding
import sru.{internal => srui}
import sru.{Type => ScalaType}

import scala.reflect.runtime.universe.TypeTag
import scala.collection.mutable

object ScalaTyping {
  sealed abstract trait TypeHole[A <: String] // TODO make type hole traits extend this
}
import ScalaTyping._

trait ScalaTyping extends Base with TraceDebug {
self: IntermediateBase => // for 'repType' TODO rm
  
  type TypSymbol = sru.TypeSymbol
  //type TypeRep = ScalaType
  implicit class TypeRep(val tpe: ScalaType) {
    override def toString = sru.show(tpe)
    override def equals(that: Any) = that.isInstanceOf[TypeRep] && that.asInstanceOf[TypeRep].tpe =:= tpe
    override def hashCode: Int = tpe.hashCode
  }
  object TypeRep { def unapply(t: TypeRep) = Some(t.tpe) }
  implicit def toScala(tr: TypeRep): ScalaType = tr.tpe // TODO rm
  case class ExtractedType(val vari: Variance, override val tpe: ScalaType) extends TypeRep(tpe) {
    override def toString = s"${vari symbol}$tpe"
  }
  override def mergeTypes(a: TypeRep, b: TypeRep): Option[ExtractedType] = (a -> b match {
    case ExtractedType(Invariant, a) -> ExtractedType(Invariant, b) => if (a =:= b) Some(Invariant, a) else None
    case ExtractedType(Invariant, a) -> ExtractedType(Covariant, b) => if (b <:< a) Some(Invariant, a) else None
    case ExtractedType(Invariant, a) -> ExtractedType(Contravariant, b) => if (a <:< b) Some(Invariant, a) else None
    case ExtractedType(Covariant, a) -> ExtractedType(Covariant, b) => Some(Covariant, sru.lub(a::b::Nil))
    case ExtractedType(Contravariant, a) -> ExtractedType(Contravariant, b) => Some(Contravariant, sru.glb(a::b::Nil))
    case ExtractedType(Covariant, a) -> ExtractedType(Contravariant, b) => Some(Invariant, a) // arbitrary!
    // ^ Note that picking `b` instead of `a` is also possible, but seems to create problems;
    // e.g. in ClassEmbeddingTests.test("Online Lowering and Normalization") where the BindingNormalizer matches redexes
    //      so if the value is null of type Null(null) is will unify to this instead of the parameter type.
    case (a: ExtractedType) -> (b: ExtractedType) => mergeTypes(b, a) map { case ExtractedType(v,t) => v -> t }
    case _ => die
  }) map ExtractedType.tupled alsoApply_? { case None => debug(s"Could not merge types $a and $b") }
  
  def uninterpretedType[A: TypeTag]: TypeRep = sru.typeTag[A].tpe
  
  
  //def typeApp(self: Rep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = sru.internal.typeRef(repType(self), typ, targs map (_ tpe))
  val FunSym2 = loadTypSymbol("scala.Function1") // TODO unify
  def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
    (typ, targs map (_ tpe)) match {
      //case (`funSym`, RecordType(params @ _*) :: ret :: Nil) => ruh.FunctionType(params map (_ _2): _*)(ret)
      case (FunSym2, RecordType(params @ _*) :: ret :: Nil) => ruh.FunctionType(params map (_ _2): _*)(ret)
      case _ => sru.internal.typeRef(self, typ, targs map (_ tpe))
    }
  }
  def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = {
    assert(typ.isStatic)
    sru.internal.typeRef(typ.owner.asType.toType, typ, targs map (_ tpe))
  }
  
  def recordType(fields: List[(String, TypeRep)]): TypeRep = {
    // TODO cache stuff
    import sru._
    import sru.{internal => inl}
    import inl.{reificationSupport => reif}
    val reftSymdef = reif.newNestedSymbol(srum.staticModule("squid.ir.ScalaTyping"), TypeName.apply("<refinement>"), NoPosition, NoFlags, true)
    val syms = fields map {
      case (name,typ) =>
        val symdef = reif.newNestedSymbol(reftSymdef, TermName(name), NoPosition, /*internal.reificationSupport.FlagsRepr.apply(138412112L)*/NoFlags, false);
        reif.setInfo[Symbol](symdef, reif.NullaryMethodType(typ));
        symdef
    }
    val reftp = reif.RefinedType(Nil, reif.newScopeWith(syms: _*), reftSymdef)
    reif.setInfo[Symbol](reftSymdef, reftp)
    reftp
  }
  object RecordType {
    import sru._
    def unapplySeq(tpe: ScalaType): Option[List[(String,Type)]] = tpe match {
      case RefinedType(Nil, scp) =>
        Some(scp map { s =>
          val tp = s.typeSignature match { case NullaryMethodType(tp) => tp }
          s.name.toString -> tp
        } toList)
      case _ => None
    } 
  }
  
  
  def constType(value: Any, underlying: TypeRep): TypeRep = constType(value)
  def constType(value: Any): TypeRep = sru.internal.constantType(sru.Constant(value))
  
  
  def typeHole(name: String): TypeRep = TypeHoleRep(name)
  
  
  
  def typLeq(a: TypeRep, b: TypeRep): Boolean = a <:< b
  def weakTypLeq(a: TypeRep, b: TypeRep, va: Variance = Covariant): Boolean = extractType(a, b, va).isDefined
  
  /* // breaks scalac...
  lazy val (funOwnerType, funSym) = {
    val sym = sru.symbolOf[Any => Any]
    (sym.owner.asType.toType, sym)
  }
  */
  // TODO make `funType` accept mutli params and call it `lambdaType`
  lazy val funSym = sru.symbolOf[Any => Any]
  lazy val funOwnerType = funSym.owner.asType.toType
  //def funType(paramt: TypeRep, bodyt: TypeRep): TypeRep = srui.typeRef(funOwnerType, funSym, paramt.tpe :: bodyt.tpe :: Nil)
  //def funType(paramt: TypeRep, bodyt: TypeRep): TypeRep = typeApp(hole("LOLOL", funOwnerType), funSym, paramt :: bodyt :: Nil)
  def lambdaType(paramTyps: List[TypeRep], ret: TypeRep): TypeRep =
    ruh.FunctionType(paramTyps map (_ tpe): _*)(ret)
  
  
  object TypeHoleRep {
    import sru._
    def apply(name: String) =
      srui.typeRef(typeOf[ScalaTyping.type], symbolOf[TypeHole[_]], srui.constantType(Constant(name)) :: Nil)
    //def unapply(tp: TypeRep) = tp.tpe match {
    def unapply(tp: Type) = tp match {
      case ht @ TypeRef(_, sym, arg :: Nil) if sym == symbolOf[TypeHole[_]] =>
        //debug(arg,arg.getClass)
        arg match {
          case ConstantType(sru.Constant(name: String)) =>
            Some(name)
          case _ => 
            System.err.println(s"Warning: hole type `$ht` has been widened.")
            None
        }
      case _ => None
    }
  }
  def hasHoles(tp: TypeRep) = tp exists { case TypeHoleRep(_) => true  case _ => false }
  
  def extractType(self: TypeRep, other: TypeRep, va: Variance): Option[Extract] = {
    import sru._
    import ruh._
    
    debug(s"$va Match $other with $self")
    nestDbg { self.tpe -> other.tpe match {
      // TODO thisType, constantType
        
      case TypeHoleRep(name) -> _ => Some(Map(), Map(name -> ExtractedType(va, other)), Map())
        
      case RefinedType(ps0, scp0) -> PossibleRefinement(ps1, scp1) =>
        if (ps0.size != ps1.size) return None
        val ps = (ps0.iterator zipAnd ps1){extractType(_,_,va)}
        val syms1 = mutable.HashMap(scp1 map (s => s.name -> s) toSeq: _*)
        val scp = scp0.iterator flatMap { s0 =>
          val s1 = syms1 getOrElse (s0.name, return None)
          if (s0.alternatives.size != s1.alternatives.size) return None
          (s0.alternatives zipAnd s1.alternatives) {
            case (s0,s1) => extractType(s0.typeSignature, s1.typeSignature, va)
          }
        }
        mergeAll(ps ++ scp)
        
      //case TypeRef(tp0, sum0, targs0) -> xtyp =>
      case typ -> xtyp => // FIXME: is it okay to do this here? we should probably ensure typ is a TypeRef...
        val targs = typ.typeArgs
        
        if (xtyp.typeSymbol.isParameter) return None alsoDo debug(s"Cannot match parameter type `$xtyp`.")
        // ^ Sometimes we get this kind of types because of type-tag-based uninterpretedType
        
        if (xtyp =:= ruh.Null) return None alsoDo debug(s"Cannot match type `Null`.") // TODO  actually allow this match (but soundly)
        
        def erron = None alsoDo debug(s"Method `baseType` returned an erroneous type.")
        
        if (va == Contravariant && xtyp.typeSymbol != typ.typeSymbol) {
        
          val baseTargs = typ.baseType(xtyp.typeSymbol) match {
            case NoType =>
              debug(s"$va $typ is not an instance of ${xtyp.typeSymbol}")
              if (typ <:< xtyp) {
                debug(s"... but $typ is still somehow a subtype of ${xtyp}")
                //assert(Any <:< xtyp,
                //  s"$typ <:< $xtyp but !($xtyp >:> Any) and ${xtyp.typeSymbol} is not a base type of $typ")
              assert(typ <:< ruh.Nothing,
                s"$typ <:< $xtyp but !($typ <:< Nothing) and ${xtyp.typeSymbol} is not a base type of $typ")
                Stream continually ruh.Nothing
              }
              else return None
            case base if base |> isErroneous => return erron
            case base =>
              debug(s"$va $typ is an instance of ${xtyp.typeSymbol} as '$base'")
              base.typeArgs.toStream
          }
          
          if (isDebugEnabled) {
            val ets = baseTargs zip xtyp.typeArgs zip (xtyp.typeSymbol.asType.typeParams map (Variance of _.asType) map (_ * va))
            if (ets nonEmpty) debug(s"$va Extr Targs(contra case): "+(ets mkString " "))
          }
          
          assert(!baseTargs.hasDefiniteSize || xtyp.typeArgs.size == baseTargs.size)
          
          val extr = (baseTargs zip xtyp.typeArgs zip xtyp.typeSymbol.asType.typeParams) map {
            case ((a,b), p) => extractType(a, b, (Variance of p.asType) * va) getOrElse (return None) }
          
          val extr2 = targs zip typ.typeSymbol.asType.typeParams map {case(ta,tp) => /*Variance.of(tp.asType) match {
            //case Covariant | Invariant => extractType(ta, Nothing, Contravariant)
            case Covariant | Invariant => extractType(ta, Nothing, Covariant)
            case Contravariant => extractType(ta, Any, Contravariant)
          }*/
            //extractType(ta, Nothing, Covariant)
            extractType(ta, Any, Contravariant) // FIXME should really be the interval 'LB..HB'
          } map (_  getOrElse (return None)) //filter (_ => false)
          
          Some((extr ++ extr2).foldLeft[Extract](Map(), Map(), Map()){case(acc,a) => merge(acc,a) getOrElse (return None)})
          
        } else if (va == Invariant && xtyp.typeSymbol != typ.typeSymbol) {
          
          debug(s"${xtyp.typeSymbol} and ${typ.typeSymbol} cannot be matched invariantly")
          None
          
        } else {
          
          val base = xtyp.baseType(typ.typeSymbol).orElse(NoType)
          // ^ this `.orElse(NoType)` seems to semantically do nothing; in fact, it will convert a NoType in the wrong 
          // universe to a NoType in our current universe so that the comparison below `base == NoType` works correctly.
          // The reason we sometimes get types from different universes (a.k.a. alien types) is too gruesome to be explained here.
          
          val baseTargs = if (base == NoType) {
            debug(s"$xtyp not an instance of ${typ.typeSymbol}")
            
            if (xtyp <:< typ) {
              debug(s"... but $xtyp is still somehow a subtype of ${typ}")
              assert((xtyp <:< ruh.Nothing) || (xtyp <:< ruh.Null),
                s"$xtyp <:< $typ but !($xtyp <:< Nothing) and ${typ.typeSymbol} is not a base type of $xtyp")
              
              Stream continually ruh.Nothing
            }
            else return None
          }
          else if (base |> isErroneous) return erron
          else base.typeArgs.toStream
          
          if (isDebugEnabled) {
            val ets = targs zip baseTargs zip (typ.typeSymbol.asType.typeParams map (Variance of _.asType) map (_ * va))
            if (ets nonEmpty) debug(s"$va Extr Targs: " + (ets mkString " "))
          }
          
          assert(!baseTargs.hasDefiniteSize || targs.size == baseTargs.size, s"$baseTargs $targs")
          
          val extr = (targs zip baseTargs zip typ.typeSymbol.asType.typeParams) map {
            case ((a,b), p) => extractType(a, b, (Variance of p.asType) * va) getOrElse (return None) }
          
          //dbg("EXTR",extr)
          Some(extr.foldLeft[Extract](Map(), Map(), Map()){case(acc,a) => merge(acc,a) getOrElse (return None)})
        }
        
        
    }}
    
  }
  
  /** Note: will _not_ try to special-case type holes (encoded as normal Scala types...)
    * This is because reinterpreted types are not usually from extractor terms -- however, this assumption might turn wrong at some point */
  def reinterpretType(tr: TypeRep, newBase: Base): newBase.TypeRep = {
    val modEmb = new ModularEmbedding[sru.type,newBase.type](sru, newBase, debug = x => debug(x))
    modEmb.liftType(tr.tpe)
  }
  
  
  def nullValue[T: CodeType]: Code[T,{}] = {
    val tp = implicitly[CodeType[T]].rep.tpe |>=? {
      case TypeHoleRep(name) => throw new IllegalArgumentException("Type hole has no known nullValue.")
    }
    Code[T,{}](const(
      if (tp <:< sru.typeOf[Unit]) NULL_UNIT
      else if (tp <:< sru.typeOf[Bool]) NULL_BOOL
      else if (tp <:< sru.typeOf[Char]) NULL_CHAR
      else if (tp <:< sru.typeOf[Byte]) NULL_BYTE
      else if (tp <:< sru.typeOf[Short]) NULL_SHORT
      else if (tp <:< sru.typeOf[Int]) NULL_INT
      else if (tp <:< sru.typeOf[Long]) NULL_LONG
      else if (tp <:< sru.typeOf[Float]) NULL_FLOAT
      else if (tp <:< sru.typeOf[Double]) NULL_DOUBLE
      else {
        val N = sru.typeOf[Null]
        assert(N <:< tp || tp <:< N, // second case is for the stupid literal type Null(null)
          s"$tp is not nullable nor .")
        NULL_NULL
      }
    ))
  }
  
  private var NULL_UNIT: Unit = _
  private var NULL_BOOL: Bool = _
  private var NULL_CHAR: Char = _
  private var NULL_BYTE: Byte = _
  private var NULL_SHORT: Short = _
  private var NULL_INT: Int = _
  private var NULL_LONG: Long = _
  private var NULL_FLOAT: Float = _
  private var NULL_DOUBLE: Double = _
  private var NULL_NULL: Null = _
  
  
}







