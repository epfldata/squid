package squid
package scback

import ch.epfl.data.sc._
import ch.epfl.data.sc.pardis.deep.scalalib.ScalaPredefIRs.Println
import ch.epfl.data.sc.pardis.deep.scalalib.ScalaPredefOps
import ch.epfl.data.sc.pardis.ir.PardisFunArg
import ch.epfl.data.sc.pardis.types.PardisType
import pardis._
import squid.utils._

import scala.collection.mutable
import squid.ir.IRException
import squid.quasi.DefaultQuasiConfig
import squid.utils.CollectionUtils.TraversableOnceHelper
import squid.utils.meta.{RuntimeUniverseHelpers => ruh}

import scala.reflect.runtime.{universe => sru}
import scala.language.existentials


/** PardisIR that uses an `AutoBinder` to associate shallow method symbols to their deep embedding,
  * and special-cases a few core methods */
class AutoboundPardisIR[DSL <: ir.Base](val DSL: DSL) extends PardisIR(DSL) {
  var ab: AutoBinder[DSL.type, this.type] = _
  
  override object Predef extends Predef[DefaultQuasiConfig] {
    implicit def conv[A](x: R[A]): Code[A,{}] = `internal Code`(x)
    implicit def convVar[A](x: sc.Var[A]): Code[squid.lib.Var[A],{}] = `internal Code`(x)
    def mkVar[T](init: Code[T,{}]): sc.Var[T] = sc.__newVar[Any](init.rep |> toExpr)(init.rep.typ).asInstanceOf[sc.Var[T]]
    def mapLambda[T:CodeType,C](x: Code[T,C])(f: R[T] => R[T]) = block(`internal Code`[T,C](f(x.toRep)))
  }
  
  implicit class PardisIROps[T](private val self: Code[T,_]) {
    def toRep: sc.Rep[T] = toExpr(self.rep).asInstanceOf[sc.Rep[T]]
  }
  
  protected val ImperativeSymbol = loadMtdSymbol(loadTypSymbol("squid.lib.package$"), "Imperative", None)
  protected val IfThenElseSymbol = loadMtdSymbol(loadTypSymbol("squid.lib.package$"), "IfThenElse", None)
  
  protected val VarApplySymbol = loadMtdSymbol(loadTypSymbol("squid.lib.package.Var$"), "apply", None)
  protected val VarBangSymbol = loadMtdSymbol(loadTypSymbol("squid.lib.package.Var"), "$bang", None)
  protected val VarColonEqualSymbol = loadMtdSymbol(loadTypSymbol("squid.lib.package.Var"), "$colon$eq", None)
  
  protected val PrintlnSymbol = loadMtdSymbol(loadTypSymbol("scala.Predef$"), "println", None)
  
  protected val Function0ApplySymbol = loadMtdSymbol(loadTypSymbol("scala.Function0"), "apply", None)
  protected val Function2ApplySymbol = loadMtdSymbol(loadTypSymbol("scala.Function2"), "apply", None)
  protected val Function3ApplySymbol = loadMtdSymbol(loadTypSymbol("scala.Function3"), "apply", None)
  
  protected val BooleanAnd = loadMtdSymbol(loadTypSymbol("scala.Boolean"), "$amp$amp", None)
  protected val BooleanOr = loadMtdSymbol(loadTypSymbol("scala.Boolean"), "$bar$bar", None)
  
  /** Note: we have to wrap every method call (and corresponding statements) inside a Block.
    * It would work to simply let all expressions reify themselves in the enclosing block, but then we lose original
    * names (let-binding gets a symbol as the value and has to withSubs(bound -> sym)).
    * And original names are currently important for `rewriteRep` to distinguish explicitly-bound variables.
    * This is why we put everything in a block, and then in `letin` rewrites blocks that return a symbol use the value
    * bound in the let-in instead of that symbol. */
  def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = {
    //println("METHOD "+mtd.name+" in "+mtd.owner)
    assert(ab =/= null, s"The AutoBinder variable `ab` in $this has not been initialized.")
    
    lazy val methodName = mtd.name.toString
    lazy val fullMethodName = mtd.fullName
    
    mtd match {
        
      case ImperativeSymbol =>
        return blockWithType(tp) {
          val ArgList(efs @ _*)::Args(r)::Nil = argss
          efs foreach toExpr
          r
        }
        
      // The autobinder does not see deep `println`, as it is not defined in an object (but directly in the cake!)
      case PrintlnSymbol => sc match {
        case ir: ScalaPredefOps => return blockWithType(types.UnitType)(Println(argss.head.reps.head |> toExpr))
        case _ => throw IRException("This IR does not extend `ScalaPredefOps` and thus does not support `println`.") }
        
      case IfThenElseSymbol =>
        //val Args(cond, thn, els)::Nil = argss
        //return ir.__ifThenElse(cond.asInstanceOf[R[Bool]], thn, els)(tp.asInstanceOf[TR[Any]])
        
        // Crashes Scalac:
        //val Args(cond, TopLevelBlock(thn), TopLevelBlock(els))::Nil = argss
        //val (cond,thn,els) = argss match { case Args(cond, TopLevelBlock(thn), TopLevelBlock(els))::Nil => (cond,thn,els) } 
        
        val Args(cond, thn: sc.Block[Any @unchecked], els: sc.Block[Any @unchecked])::Nil = argss
        return blockWithType(tp)(sc.IfThenElse(toExpr(cond).asInstanceOf[R[Bool]], thn, els)(tp))
        
      case Function0ApplySymbol =>
        return blockWithType(tp)(sc.__app(toExpr(self).asInstanceOf[R[()=>Any]])(tp.asInstanceOf[TR[Any]])())
        
      case Function1ApplySymbol =>
        val arg = argss.head.asInstanceOf[Args].reps.head
        return blockWithType(tp)(sc.__app(toExpr(self).asInstanceOf[R[Any=>Any]])(arg.typ, tp.asInstanceOf[TR[Any]])(arg |> toExpr))
        
      case Function2ApplySymbol =>
        val Args(a0,a1)::Nil = argss
        return blockWithType(tp)(sc.__app(toExpr(self).asInstanceOf[R[(Any,Any)=>Any]])(a0.typ, a1.typ, tp.asInstanceOf[TR[Any]])(a0 |> toExpr, a1 |> toExpr))
        
      case Function3ApplySymbol =>
        val Args(a0,a1,a2)::Nil = argss
        return blockWithType(tp)(sc.__app(toExpr(self).asInstanceOf[R[(Any,Any,Any)=>Any]])(a0.typ, a1.typ, a2.typ, tp.asInstanceOf[TR[Any]])(a0 |> toExpr, a1 |> toExpr, a2 |> toExpr))
        
      case VarApplySymbol =>
        val arg = argss.head.asInstanceOf[Args].reps.head
        return blockWithType(arg.typ)(sc.__newVar[Any](toExpr(arg))(arg.typ))
        
      case VarBangSymbol =>
        val v = toVar(self)
        return blockWithType(tp)(sc.__readVar[Any](v)(tp))
        
      case VarColonEqualSymbol =>
        val v = toVar(self)
        val Args(arg)::Nil = argss
        return blockWithType(tp)(sc.__assign[Any](v, arg |> toExpr)(v.e.tp))
        
      case _ if fullMethodName == "squid.lib.And" =>
        val Args(a,b)::Nil = argss
        return methodApp(a, BooleanAnd, Nil, Args(b)::Nil, BooleanType)
        
      case _ if fullMethodName == "squid.lib.Or" =>
        val Args(a,b)::Nil = argss
        return methodApp(a, BooleanOr, Nil, Args(b)::Nil, BooleanType)
        
      case _ if methodName == "$eq$eq" =>
        val Args(a)::Nil = argss
        return blockWithType(types.BooleanType)(sc.infix_==(self |> toExpr, a |> toExpr)(self.typ, a.typ))
        
      case _ if methodName == "$bang$eq" =>
        val Args(a)::Nil = argss
        return blockWithType(types.BooleanType)(sc.infix_!=(self |> toExpr, a |> toExpr)(self.typ, a.typ))
        
      case _ if methodName == "$hash$hash" =>
        //assert(argss.isEmpty)
        assert(argss == List(Args()))
        return blockWithType(types.IntType)(sc.infix_hashCode(self |> toExpr)(self.typ))
        
      case _ if methodName == "toString" =>
        assert(argss == List(Args()))
        return blockWithType(types.StringType)(sc.infix_toString(self |> toExpr)(self.typ))
        
      case _ if methodName == "asInstanceOf" =>
        assert(argss == Nil)
        val targ::Nil = targs
        return blockWithType(targ)(sc.infix_asInstanceOf(self |> toExpr)(targ))
        
      case _ =>
    }
    
    val mk = ab.map.getOrElse(mtd, throw IRException(
      s"Could not find a deep representation for $mtd${mtd.typeSignature} in ${mtd owner}; perhaps it is absent from the DSL cake or the auto-binding failed."))
    
    blockWithType(tp){
    
    assert(argss.size == mtd.paramLists.size)
    def argsTail = (argss zip mtd.paramLists) flatMap { case (as,ps) =>
      val (nonRepeatedReps, repeatedReps) = as match {
        // FIXMElater: will fail on ArgsVarargSpliced
        case Args(as @ _*) =>
          assert(as.size == ps.size)
          (as, Nil)
        case ArgsVarargs(as,vas) =>
          assert(as.reps.size+1 == ps.size)
          (as.reps,vas.reps)
      }
      (nonRepeatedReps zipAnd ps) { (a, p) => p.typeSignature match {
        case sru.TypeRef(_, ruh.ByNameParamClass, tp) => a |> toBlock
        case _ if { // Check for Scala Boolean's && and || as the by-name behavior is not exposed in their signature!!
          val name = mtd.fullName.toString 
          name == "scala.Boolean.$amp$amp" || name == "scala.Boolean.$bar$bar"
        } => a |> toBlock
        case _ => a |> toExpr
      }} ++ (repeatedReps map toExpr) // Note: repeated parameters cannot be by-name
    }
    
    val args = self match {
      case New(_) => assert(targs isEmpty); argsTail
      case null => argsTail
      case _ => (self |> toExpr) :: argsTail
    }
    
    //println("Args: "+args)
    
    type TRL = sc.TypeRep[Any] |> List
    
    // Method makers currently call toAtom; we don't need to do it here.
    mk(args.asInstanceOf[List[PardisFunArg]],
      // `self` will be null if it corresponds to a static module (eg: `Seq`)
      // in that case, the method type parameters are expected to be passed in first position:
      (targs optionIf (self == null)
             Else self.typ.typeArguments
        ).asInstanceOf[TRL],
      targs.asInstanceOf[TRL])
    
    }
    
  }
  
  def nullValue[T: CodeType]: Code[T,{}] = Code(const((implicitly[CodeType[T]].rep:PardisType[_]) match {
    case types.UnitType => ()
    case types.BooleanType => false
    case types.CharacterType => '\u0000'
    case types.ByteType => 0:Byte
    case types.ShortType => 0:Short
    case types.IntType => 0
    case types.LongType => 0L
    case types.FloatType => 0F
    case types.DoubleType => 0D
    case _ => null
  }))
  
}


