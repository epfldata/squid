package squid
package anf.analysis

import squid.ir.SimpleANF
import squid.lang.InspectableBase
import utils._

/**
  * Created by lptk on 10/02/17.
  */
trait BlockHelpers extends SimpleANF { self => // TODO don't make it a Base mixin...
  
  /** Matches expressions that have no subexpressions; note that it does NOT match x.module where `module` is the name
    * of a nested object and `x` is not a static path. */
  object LeafCode {
    def unapply[T,C](q: Code[T,C]): Option[Code[T,C]] = q.rep.dfn match {
      case (_:Constant) | (_:Hole) | (_:SplicedHole) | (_:StaticModule) | (_:BoundVal) => Some(q)
      case Ascribe(t,_) => unapply(Code(t))
      case _ => None
    }
  }
  
  object Lambda {
    def unapply[T,C](q: Code[T,C]): Option[Lambda[T,C]] = q.rep.dfn match {
      case (abs:Abs) => Some(new Lambda[T,C](abs,None)) // TODO ascr
      case Ascribe(t,_) => unapply(Code(t))
      case _ => None
    }
  }
  class Lambda[T,C](private val abs: Abs, private val asc: Option[TypeRep]) {
    type C0 <: C
    val body: Code[T,C0] = Code(abs.body)
    def rebuild[R](newBody: Code[R,C0]): Code[R,C] = {
      val res = rep(Abs(abs.param, newBody.rep)(abs.typ))
      Code(asc map (Ascribe(res, _) |> rep) getOrElse res)
    }
  }
  
  object MethodApplication {
    def unapply[T,C](q: Code[T,C]): Option[MethodApplication[T,C]] = unapplyMethodApplication[T,C](q)
  }
  def unapplyMethodApplication[T,C](q: Code[T,C], tp: Option[TypeRep] = None): Option[MethodApplication[T,C]] = {
    q.rep.dfn match {
      case app: MethodApp => Some(new MethodApplication(app,tp))
      case Ascribe(e,t) => unapplyMethodApplication(Code(e),tp orElse Some(t))
      case _ => None
    }
  }
  class MethodApplication[T,C](private val ma: MethodApp, private val asc: Option[TypeRep]) {
    val symbol = ma.sym
    val args: Seq[Seq[Code[Any,C]]] = List(Code(ma.self)) :: ma.argss.map(_.reps.map(Code.apply[Any,C] _))
    def rebuild(argsTransfo: SelfTransformer): Code[T,C] = {
      val res = rep(MethodApp(
        ma.self |> argsTransfo.pipeline,
        ma.sym,
        ma.targs,
        ma.argss.map(_.map(self)(argsTransfo.pipeline)),
        ma.typ
      ))
      Code(asc map (Ascribe(res, _) |> rep) getOrElse res)
    }
    override def toString: String = s"${Rep(ma)}"
  }
  
  
  abstract class AsBlock[T,C](val original: Code[T,C]) {
    type C0 <: C
    val stmts: List[Code[_,C0]]
    val res: Code[T,C0]
    
    // TODO methods for hygienically and safely performing statements manipulations, such as filtering statements based
    // on whether they depend on some context, etc.
    //def splitDependent[D:Ctx]: (List[_,D],List[_,C0]) -- or ((Block[Unit,C] => Block[Unit,C]) => Block[T,D])
    
    def statements(take: Int = stmts.size): Code[Unit,C] = 
      Code(constructBlock(original.rep.asBlock._1.take(take), () |> const))
    
    def rebuild(stmtTransfo: SelfTransformer, resultTransfo: SelfTransformer): Code[T,C]
    
    def withResult[R](r: Code[R,C0]): Code[R,C] // TODO generalize..?
    
  }
  
  object Block {
    def unapply[T,C](q: Code[T,C]): Option[AsBlock[T,C]] = unapplyBlock[T,C](q).get optionIf (_.stmts.nonEmpty)
  }
  object AsBlock {
    def unapply[T,C](q: Code[T,C]): Some[AsBlock[T,C]] = unapplyBlock[T,C](q)
  }
  def unapplyBlock[T,C](q: Code[T,C]): Some[AsBlock[T,C]] = {
    val bl = q.rep.asBlock
    // Q: is it okay to extract single expressions with this extractor?
    /*if (bl._1.isEmpty) None
    else*/ Some(new AsBlock[T,C](q) {
      val stmts: List[Code[_,C0]] = bl._1 map (_.fold(_._2, identity) |> Code.apply[T,C0])
      val res: Code[T,C0] = Code(bl._2)
      def rebuild(stmtTransfo: SelfTransformer, resultTransfo: SelfTransformer): Code[T,C] = Code(constructBlock((
        bl._1 map { case Left((v,r)) => Left(v,r |> stmtTransfo.pipeline) case Right(r) => Right(r |> stmtTransfo.pipeline) },
        bl._2 |> resultTransfo.pipeline
      )))
      def withResult[R](result: Code[R,C0]): Code[R,C] = Code(constructBlock((bl._1, result.rep)))
    })
  }
  
  object WithResult {
    def unapply[T,C](b: AsBlock[T,C]): Some[AsBlock[T,C] -> Code[T,b.C0]] = Some(b->b.res)
  }
  
  
  import Predef.QuasiContext
  import Predef.implicitType
  import squid.anf.analysis.BlockHelpers.placeHolder
  
  /** A thing of beauty: no unsafe casts, @unchecked patterns or low-level hacks; just plain typeticool Squid quasiquotes. */
  object Closure extends AbstractClosure {
    override def unapply[A:CodeType,C](term: Code[A,C]): Option[Closure[A, C]] = {
      term match {
        case code"(x: $xt) => ($body:$bt)" => // Note: here `bt` is NOT `A` -- in fact `A =:= (xt => bt)`
          Some(new ClosureImpl[A,C,Unit](code"()", code"(_:Unit) => $term"))
        case _ => super.unapply(term)
      }
    }
  }
  object GeneralClosure extends AbstractClosure {
    override def unapply[A:CodeType,C](term: Code[A,C]): Some[Closure[A, C]] = {
      Some(super.unapply(term).getOrElse {
        new ClosureImpl[A,C,Unit](code"()", code"(_:Unit) => $term")
      })
    }
  }
  class AbstractClosure {
    
    private var uid = 0
    
    //def unapply[A,C](x: IR[A,C]): Option[Closure[A,C with AnyRef]] = {
    def unapply[A:CodeType,C](term: Code[A,C]): Option[Closure[A, C]] = {
    // ^ `C with AnyRef` necessary because we do `C{x:xt} – {x} == C{} == C with AnyRef`...
      
      //println("CLOSREC: "+x.rep)
      
      term match {
          
        case code"val ClosureVar: $xt = $v; $body: A" =>
          
          // Cannot do the following, as it would confuse the matched bindings `x` -- TODO why does it not make a compile error? (probably because of unchecked patmat below)
          //val rec = unapply(body)
          
          // TODO a fixpoint combinator to help recursive binder extrusion
          
          // Note: the trick will become unneeded once proper context polymorphism hygiene is implemented (see `doc/internal/design/future/Hygienic Context Polymorphism.md`)
          
          val curid = uid alsoDo (uid += 1)
          val closedBody = body subs 'ClosureVar -> code"placeHolder[$xt](${Const(curid)})"
          val rec = unapply(closedBody)
          def reopen[T,C](q: Code[T,C]): Code[T,C{val ClosureVar:xt.Typ}] = q rewrite {
            //case dbg_ir"squid.lib.placeHolder[$$xt](${Const(Curid)})" => ir"x?:$xt"  // FIXME `Curid` pat-mat...
            case code"placeHolder[$$xt](${Const(id)})" if id == curid => code"ClosureVar?:$xt"
          }
          
          rec match {
              
            case Some(cls) if cls.env =~= code"()" =>
              import cls.{typA => _, _}
              Some(new ClosureImpl(v, code"(ClosureVar:$xt) => ${reopen(fun)}(${reopen(env)})")) // type: ClosureImpl[A,C with AnyRef,xt.Typ]
              
            case Some(cls) =>
              import cls.{typA => _, _}
              Some(new ClosureImpl(  // type: ClosureImpl[A, C with AnyRef, (xt.Typ,cls.E)]
                code"val ClosureVar = $v; (ClosureVar,${reopen(env)})",
                code"{ (env:($xt,${typE})) => val ClosureVar = env._1; ${reopen(fun)}(env._2) }"))
              
            case None => None
          }
        case _ =>
          None
      }
    }
    
  }
  abstract class Closure[A,-C] {
    type E
    val env: Code[E,C]
    val fun: Code[E => A,C]
    implicit val typA: CodeType[A]
    implicit val typE: CodeType[E]
  }
  private case class ClosureImpl[A,C,TE](env: Code[TE,C], fun: Code[TE => A,C])(implicit val typA: CodeType[A], val typE: CodeType[TE])
    extends Closure[A,C] { type E = TE }
  
  
  
  
  // This class is here because it uses BlockHelpers, and because of Scala peth-dependent typing limitations, there is
  // no easy way to have it defined outside. This could be resolved by making BlockHelpers NOT a mixin trait, which it
  // should never have been anyways. (TODO change it)
  import ir._
  trait ANFTypeChangingCodeTransformer extends SelfTransformer with TypeChangingCodeTransformer { self =>
    def transformChangingType[T,C](code: Code[T,C]): Code[_,C] = code match {
      case Lambda(lmd) => lmd.rebuild(transformChangingType(lmd.body))
      case MethodApplication(m) => m.rebuild(this)
      case LeafCode(_) => code
    }
    
  }
  
}
object BlockHelpers {
  import squid.lib.transparencyPropagating
  /** Making it `private` ensures that an end program which would still (erroneously) contain it would not be able to compile.
    * Note: using an implicit-based scheme could even give a more helpful compile-time error message. */
  @transparencyPropagating private def placeHolder[T](id: Int): T = squid.lib.placeHolder("Closure")
}

