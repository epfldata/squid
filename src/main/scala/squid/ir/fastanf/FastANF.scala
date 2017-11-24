package squid
package ir.fastanf

import utils._
import lang.{Base, InspectableBase, ScalaCore}
import squid.ir._

import scala.collection.immutable.{ListMap, ListSet}

class FastANF extends InspectableBase with CurryEncoding with StandardEffects with ScalaCore {
  private[this] implicit val base = this
  
  
  // * --- * --- * --- *  Basic Definitions * --- * --- * --- *
  
  type Rep = ir.fastanf.Rep
  type TypeRep = ir.fastanf.TypeRep
  type BoundVal = ir.fastanf.Symbol
  type TypSymbol = TypeSymbol
  type MtdSymbol = MethodSymbol
  
  
  // * --- * --- * --- *  Reification  * --- * --- * --- *
  
  var scopes: List[ReificationContext] = Nil
  
  @inline final def wrap(r: => Rep, inXtor: Bool): Rep = {
    val scp = new ReificationContext(inXtor)
    scopes ::= scp
    try scp.finalize(r)
    finally scopes = scopes.tail
  }
  @inline final def wrapNest(r: => Rep): Rep = {
    wrap(r, currentScope.inExtractor)
  }
  override final def wrapConstruct(r: => Rep): Rep = wrap(super.wrapConstruct(r), false)
  override final def wrapExtract(r: => Rep): Rep = wrap(super.wrapExtract(r), true)
  
  @inline final def currentScope = scopes.head
  
  def toArgumentLists(argss: List[ArgList]): ArgumentLists = {
    // Note: some arguments may be let-bindings (ie: blocks), which is only possible if they are by-name arguments
    
    def toArgumentList(args: Seq[Rep]): ArgumentList =
      args.foldRight(NoArguments: ArgumentList)(_ ~: _)
    def toArgumentListWithSpliced(args: Seq[Rep])(splicedArg: Rep) =
      args.foldRight(SplicedArgument(splicedArg): ArgumentList)(_ ~: _)
    
    argss.foldRight(NoArgumentLists: ArgumentLists) {
      (args, acc) => args match {
        case Args(as @ _*) => toArgumentList(as) ~~: acc
        case ArgsVarargs(Args(as @ _*), Args(bs @ _*)) => toArgumentList(as ++ bs) ~~: acc // ArgVararg ~converted as Args!
        case ArgsVarargSpliced(Args(as @ _*), s) => toArgumentListWithSpliced(as)(s) ~~: acc
      }
    }
  }
  
  def toListOfArgList(argss: ArgumentLists): List[ArgList] = {
    def toArgList(args: ArgumentList): List[Rep] -> Option[Rep] = args match {
      case NoArguments => Nil -> None
      case SplicedArgument(a) => Nil -> Some(a) // Everything after spliced argument is ignored.
      case r : Rep => List(r) -> None
      case ArgumentCons(h, t) =>
        val (rest, spliced) = toArgList(t)
        (h :: rest) -> spliced
    }

    argss match {
      case ArgumentListCons(h, t) =>
        val (args, spliced) = toArgList(h)
        val _args = Args(args: _*)
        spliced.fold(_args: ArgList)(s => ArgsVarargSpliced(_args, s)) :: toListOfArgList(t)
      case NoArgumentLists => Nil
      case SplicedArgument(spliced) => List(ArgsVarargSpliced(Args(), spliced)) // Not sure
      case ac : ArgumentCons =>
        val (args, spliced) = toArgList(ac)
        val _args = Args(args: _*)
        spliced.fold(_args: ArgList)(s => ArgsVarargSpliced(_args, s)) :: Nil
      case NoArguments => Nil
      case r : Rep => List(Args(r))
    }
  }
  
  
  // * --- * --- * --- *  Implementations of `Base` methods  * --- * --- * --- *
  
  def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal = new UnboundSymbol(name,typ)
  def readVal(bv: BoundVal): Rep = curSub getOrElse (bv, bv)
  def const(value: Any): Rep = Constant(value)
  
  // Note: method `lambda(params: List[BoundVal], body: => Rep): Rep` is implemented by CurryEncoding
  def abs(param: BoundVal, mkBody: => Rep): Rep = {
    val body = wrapNest(mkBody)
    new Lambda(param.name, param, param.typ, body).alsoApply(param rebind _) |> letbind
  }
  def funType(paramTyp: TypeRep, ret: TypeRep): TypeRep = lambdaType(paramTyp :: Nil, ret)
  def lambdaType(paramTyps: List[TypeRep], ret: TypeRep): TypeRep = DummyTypeRep
  
  def staticModule(fullName: String): Rep = StaticModule(fullName)
  def module(prefix: Rep, name: String, typ: TypeRep): Rep = Module(prefix, name, typ)
  def newObject(typ: TypeRep): Rep = NewObject(typ)
  def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = mtd match {
    case MethodSymbol(TypeSymbol("squid.lib.package$"), "Imperative") => argss match {
      case List(h, t) =>
        val firstArgss = h.reps
        val holes = h.reps.filter {
          case Hole(_, _) => true
          case _ => false
        }

        val lastArgss = t.reps
        assert(lastArgss.size == 1)
        holes.foldRight(lastArgss.head) { case (h, acc) =>
          letin(bindVal("tmp", h.typ, Nil), h, acc, acc.typ)
        }
    }


    case _ => MethodApp(self |> inlineBlock, mtd, targs, argss |> toArgumentLists, tp) |> letbind
  }
  def byName(mkArg: => Rep): Rep = wrapNest(mkArg)
  
  def letbind(d: Def): Rep = currentScope += d
  def inlineBlock(r: Rep): Rep = r |>=? {
    case lb: LetBinding =>
      println(s"INLINE: $lb --> $scopes")
      currentScope += lb
      println(s"$scopes")
      inlineBlock(lb.body)
  }

  override def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = {
    println(s"letin: $value --> $bound")
    value match {
      case s: Symbol =>
        s.owner |>? {
          case lb: RebindableBinding =>
            //println(s"LETIN $lb ")
            lb.name = bound.name
        }
        s.owner |>? {
          case lb: LetBinding =>
            lb.isUserDefined = true
        }
        withSubs(bound, value)(body)

      //s.owner |>? {
      //  case lb: RebindableBinding =>
      //    lb.name = bound.name
      //}
      //bound rebind s
      //body
      case lb: LetBinding =>
        // conceptually, does like `inlineBlock`, but additionally rewrites `bound` and renames `lb`'s last binding
        val last = lb.last
        val boundName = bound.name
        bound rebind last.bound
        last.body = body
        last.name = boundName // TODO make sure we're only renaming an automatically-named binding?
        lb
      // case c: Constant => bottomUpPartial(body) { case `bound` => c }
      case h: Hole =>
        //Wrap construct? How?

        // letin(x, Hole, Constant(20)) => `val tmp = defHole; 20;`

        val dh = wrapConstruct(new LetBinding(bound.name, bound, DefHole(h), bound) alsoApply bound.rebind) // flag wrapConstruct?

        //(dh |>? {
        //  case bv: BoundVal => bv.owner |>? {
        //    case lb: LetBinding =>
        //      lb.body = body
        //      lb
        //  }
        //}).flatten.getOrElse(body)

        //new LetBinding(bound.name, bound, dh, body) alsoApply (currentScope += _) alsoApply (bound.rebind)
        withSubs(bound -> dh)(body)


      case (_:HOPHole) | (_:HOPHole2) | (_:SplicedHole) =>
        ??? // TODO holes should probably be Def's; note that it's not safe to do a substitution for holes
      case _ =>
        withSubs(bound -> value)(body)
      // ^ executing `body` will reify some statements into the reification scope, and likely return a symbol
      // during this reification, we need all references to `bound` to be replaced by the actual `value`
    }
  }

  var curSub: Map[Symbol,Rep] = Map.empty
  def withSubs[R](subs: Symbol -> Rep)(k: => R): R = {
    val oldSub = curSub
    curSub += subs
    try k finally curSub = oldSub
  }

  override def tryInline(fun: Rep, arg: Rep)(retTp: TypeRep): Rep = {
    println(s"tryInline $fun -- $arg")
    fun match {
      case lb: LetBinding => lb.value match {
        case l: Lambda => letin(l.bound, arg, l.body, l.body.typ)
        case _ => super.tryInline(fun, arg)(retTp)
      }
      case _ => super.tryInline(fun, arg)(retTp)
    }
  }

  override def ascribe(self: Rep, typ: TypeRep): Rep = if (self.typ =:= typ) self else self match {
    case Ascribe(trueSelf, _) => Ascribe(trueSelf, typ) // Hopefully Scala's subtyping is transitive!
    case _ => Ascribe(self, typ)
  }

  def loadMtdSymbol(typ: TypSymbol, symName: String, index: Option[Int] = None, static: Boolean = false): MtdSymbol = MethodSymbol(typ, symName) // TODO

  object Const extends ConstAPI {
    def unapply[T: IRType](ir: IR[T,_]): Option[T] = ir.rep match {
      case cst @ Constant(v) if typLeq(cst.typ, irTypeOf[T].rep) => Some(v.asInstanceOf[T])
      case _ => None
    }
  }

  //   /** Artifact of a term extraction: map from hole name to terms, types and spliced term lists */

  def repEq(a: Rep, b: Rep): Boolean =
    (a extractRep b) === Some(EmptyExtract) && (b extractRep a) === Some(EmptyExtract)


  // * --- * --- * --- *  Implementations of `IntermediateBase` methods  * --- * --- * --- *

  def nullValue[T: IRType]: IR[T,{}] = IR[T, {}](const(null)) // FIXME: should implement proper semantics; e.g. nullValue[Int] == ir"0", not ir"null"
  def reinterpret(r: Rep, newBase: Base)(extrudedHandle: BoundVal => newBase.Rep): newBase.Rep = {
    def reinterpret0: Rep => newBase.Rep = r => reinterpret(r, newBase)(extrudedHandle)
    def reinterpretType: TypeRep => newBase.TypeRep = t => newBase.staticTypeApp(newBase.loadTypSymbol("scala.Any"), Nil)
    def reinterpretBV:BoundVal => newBase.BoundVal = bv => newBase.bindVal(bv.name, reinterpretType(bv.typ), Nil)
    def reinterpretTypSym(t: TypeSymbol): newBase.TypSymbol = newBase.loadTypSymbol(t.name)
    def reinterpretMtdSym(s: MtdSymbol): newBase.MtdSymbol = newBase.loadMtdSymbol(reinterpretTypSym(s.typ), s.name)
    def reinterpretArgList(argss: ArgumentLists): List[newBase.ArgList] = toListOfArgList(argss) map {
      case ArgsVarargSpliced(args, varargs) => newBase.ArgsVarargSpliced(args.map(newBase)(reinterpret0), reinterpret0(varargs))
      case ArgsVarargs(args, varargs) => newBase.ArgsVarargs(args.map(newBase)(reinterpret0), varargs.map(newBase)(reinterpret0))
      case args : Args => args.map(newBase)(reinterpret0)
    }
    def defToRep(d: Def): newBase.Rep = d match {
      case app @ App(f, a) => newBase.app(reinterpret0(f), reinterpret0(a))(reinterpretType(app.typ))
      case ma : MethodApp => newBase.methodApp(
        reinterpret0(ma.self),
        reinterpretMtdSym(ma.mtd),
        ma.targs.map(reinterpretType),
        reinterpretArgList(ma.argss),
        reinterpretType(ma.typ))
      case l: Lambda => newBase.lambda(List(reinterpretBV(l.bound)), reinterpret0(l.body))
      case DefHole(h) => newBase.hole(h.name, reinterpretType(h.typ))
    }

    r match {
      case Constant(v) => newBase.const(v)
      case StaticModule(fn) => newBase.staticModule(fn)
      case NewObject(t) => newBase.newObject(reinterpretType(t))
      case Hole(n, t) => newBase.hole(n, reinterpretType(t))
      case SplicedHole(n, t) => newBase.splicedHole(n, reinterpretType(t))
      case Ascribe(s, t) => newBase.ascribe(reinterpret0(s), reinterpretType(t))
      case HOPHole(n, t, args, visible) => newBase.hopHole(
        n,
        reinterpretType(t),
        args.map(_.map(reinterpretBV)),
        visible.map(reinterpretBV))
      case HOPHole2(n, t, args, visible) => newBase.hopHole2(
        n,
        reinterpretType(t),
        args.map(_.map(reinterpret0)),
        visible.map(reinterpretBV)
      )
      case Module(p, n, t) => newBase.module(reinterpret0(p), n, reinterpretType(t))
      case lb: LetBinding => newBase.letin(
        reinterpretBV(lb.bound),
        defToRep(lb.value),
        reinterpret0(lb.body),
        reinterpretType(lb.typ))
      case s: Symbol => extrudedHandle(s)
    }

  }
  def repType(r: Rep): TypeRep = r.typ
  def boundValType(bv: BoundVal): TypeRep = bv.typ
  
  
  // * --- * --- * --- *  Implementations of `InspectableBase` methods  * --- * --- * --- *

  def extractType(xtor: TypeRep, xtee: TypeRep, va: squid.ir.Variance): Option[Extract] = Some(EmptyExtract) //unsupported
  def bottomUp(r: Rep)(f: Rep => Rep): Rep = transformRepAndDef(r)(identity, f)(identity)
  def topDown(r: Rep)(f: Rep => Rep): Rep = transformRepAndDef(r)(f)(identity)
  def transformRepAndDef(r: Rep)(pre: Rep => Rep, post: Rep => Rep = identity)(preDef: Def => Def, postDef: Def => Def = identity): Rep = {
    def transformRepAndDef0(r: Rep) = transformRepAndDef(r)(pre, post)(preDef, postDef)

    def transformDef(d: Def): Def = postDef(preDef(d) match {
      case App(f, a) => App(transformRepAndDef0(f), transformRepAndDef0(a)) // Note: App is a MethodApp, but we can transform it more efficiently this way
      case ma: MethodApp => MethodApp(transformRepAndDef0(ma.self), ma.mtd, ma.targs, ma.argss argssMap (transformRepAndDef0(_)), ma.typ)
      case l: Lambda => // Note: destructive modification of the lambda binding!
        //new Lambda(l.name, l.bound, l.boundType, transformRepAndDef0(l.body))
        l.body = l.body |> transformRepAndDef0
        l
      case _ => d
    })

    post(pre(r) match {
      case lb: LetBinding => // Note: destructive modification of the let-binding!
        //new LetBinding(
        //  lb.name,
        //  lb.bound,
        //  transformDef(lb.value),
        //  transformRepAndDef0(lb.body)
        //)
        lb.value = lb.value |> transformDef
        lb.body = lb.body |> transformRepAndDef0
        lb
      case Ascribe(s, t) =>
        Ascribe(transformRepAndDef0(s), t)
      case Module(p, n, t) =>
        Module(transformRepAndDef0(p), n, t)
      case r @ ((_:Constant) | (_:Hole) | (_:Symbol) | (_:SplicedHole) | (_:HOPHole) | (_:HOPHole2) | (_:NewObject) | (_:StaticModule)) => r
    })
  }
  
  def transformRep(r: Rep)(pre: Rep => Rep, post: Rep => Rep = identity): Rep =
    transformRepAndDef(r)(pre, post)(identity, identity)

  protected def extract(xtor: Rep, xtee: Rep): Option[Extract] = {
    println(s"Extract($xtor, $xtee)")
    for {
      es <- extractWithState(xtor, xtee)(State.forExtraction(xtor, xtee)).fold(_ => None, Some(_))
      if es.mks.xtor.isEmpty && es.mks.xtee.isEmpty
    } yield es.ex
  }

  type Ctx = Map[BoundVal, BoundVal]
  def reverse[A, B](m: Map[A, B]): Map[B, Set[A]] = m.groupBy(_._2).mapValues(_.keys.toSet)
  def updateWith(m: Map[BoundVal, Set[BoundVal]])(u: (BoundVal, BoundVal)): Map[BoundVal, Set[BoundVal]] = u match {
    case (k, v) => m + (k -> (m(k) + v))
  }

  type ExtractState = Either[State, State]
  implicit def rightBias[A, B](e: Either[A, B]): Either.RightProjection[A,B] = e.right
  
  case class State(ex: Extract, ctx: Ctx, mks: Markers, matchedImpureBVs: Set[BoundVal], failedMatches: Map[BoundVal, Set[BoundVal]], makeUnreachable: Boolean) {
    def withNewExtract(newEx: Extract): State = copy(ex = newEx)
    def withCtx(newCtx: Ctx): State = copy(ctx = newCtx)
    def withCtx(p: (BoundVal, BoundVal)): State = copy(ctx = ctx + p)
    def updateMarkers(newMks: Markers): State = copy(mks = newMks)
    def withoutMarkers(xtorMk: BoundVal, xteeMk: BoundVal): State = copy(mks = Markers(mks.xtor - xtorMk, mks.xtee - xteeMk))
    def withMatchedImpures(r: Rep): State = r match {
      case lb: LetBinding if isPure(lb.body) => copy(matchedImpureBVs = matchedImpureBVs + lb.bound) withMatchedImpures lb.body
      case lb: LetBinding => this withMatchedImpures lb.body
      case bv: BoundVal => copy(matchedImpureBVs = matchedImpureBVs + bv)
      case _ => this
    } 
    def withFailed(p: (BoundVal, BoundVal)): State = copy(failedMatches = updateWith(failedMatches)(p))

    def updateExtractWith(e: Option[Extract]*)(implicit default: State): ExtractState = {
      mergeAll(Some(ex) +: e).fold[ExtractState](Left(default))(ex => Right(this withNewExtract ex))
    }
  }
  object State {
    def forRewriting(xtor: Rep, xtee: Rep): State = State(xtor, xtee, true)
    def forExtraction(xtor: Rep, xtee: Rep): State = State(xtor, xtee, false)
    
    private def apply(xtor: Rep, xtee: Rep, makeUnreachable: Bool): State = 
      State(EmptyExtract, ListMap.empty, Markers(xtor, xtee), Set.empty, Map.empty.withDefaultValue(Set.empty), makeUnreachable)
  }

  sealed trait Marker
  case object EndPoint extends Marker
  case object NonEndPoint extends Marker

  case class Markers(xtor: ListSet[BoundVal], xtee: ListSet[BoundVal]) {
    private def marker(ls: ListSet[BoundVal])(bv: BoundVal) = if (ls contains bv) EndPoint else NonEndPoint
    def xtorMarker(bv: BoundVal): Marker = marker(xtor)(bv)
    def xteeMarker(bv: BoundVal): Marker = marker(xtee)(bv)
  }
  object Markers {
    def apply(xtor: Rep, xtee: Rep): Markers = Markers(extractionStarts(xtor), extractionStarts(xtee))

    private def extractionStarts(r: Rep): ListSet[BoundVal] = {
      def bvs(d: Def, acc: ListSet[BoundVal]): ListSet[BoundVal] = d match {
        case _: Lambda => ListSet.empty // TODO The lambda may never be applied.
        case ma: MethodApp => (ma.self :: ma.argss.argssList).foldLeft(acc) {
          case (acc, bv: BoundVal) => acc - bv
          case (acc, _) => acc // Assuming no LBs in self or argument positions
        }
        case _ => ListSet.empty
      }

      def extractionStarts0(r: Rep, acc: ListSet[BoundVal]): ListSet[BoundVal] = r match {
        case lb: LetBinding => effect(lb) match {
          case Pure => extractionStarts0(lb.body, bvs(lb.value, acc + lb.bound))
          case Impure => extractionStarts0(lb.body, bvs(lb.value, acc))
        }
        case bv: BoundVal => acc - bv
        case _ => acc
      }

      extractionStarts0(r, ListSet.empty)
    }
  }

  def extractWithState(xtor: Rep, xtee: Rep)(implicit es: State): ExtractState = {
    def extractHOPHole(name: String, typ: TypeRep, argss: List[List[Rep]], visible: List[BoundVal])(implicit es: State): ExtractState = {
      println("EXTRACTINGHOPHOLE")
      type Func = List[List[BoundVal]] -> Rep
      def emptyFunc(r: Rep) = List.empty[List[BoundVal]] -> r
      def fargss(f: Func) = f._1
      def fbody(f: Func) = f._2

      def replaceBVs(r: Rep)(f: BoundVal => BoundVal): Rep = r match {
        case bv: BoundVal => f(bv)
        case lb: LetBinding =>
          lb.value = replaceBVsInDef(lb.value)(f)
          lb
        case _ => r
      }

      def replaceBVsInDef(d: Def)(f: BoundVal => BoundVal): Def = {
        println(s"CHANGEDDEF: $d")
        d match {
          case ma: MethodApp =>
            MethodApp(
              replaceBVs(ma.self)(f),
              ma.mtd,
              ma.targs,
              ma.argss.argssMap(r => replaceBVs(r)(f)),
              ma.typ
            )

          case l: Lambda =>
            new Lambda(
              l.name,
              l.bound,
              l.boundType,
              replaceBVs(l.body)(f)
            )

          case _ => d
        }
      }

      def hasUndeclaredBVs(r: Rep): Boolean = {
        println(s"Checking $r")
        def hasUndeclaredBVs0(r: Rep, declared: Set[BoundVal]): Boolean = r match {
          case bv: BoundVal => !(declared contains bv)
          case lb: LetBinding =>
            val declared0 = declared + lb.bound
            hasUndeclaredBVsinDef(lb.value, declared0) || hasUndeclaredBVs0(lb.body, declared0)
          case _ => false
        }

        def hasUndeclaredBVsinDef(d: Def, declared: Set[BoundVal]): Boolean = d match {
          case l: Lambda => hasUndeclaredBVs0(l.body, declared + l.bound)
          case ma: MethodApp => (ma.self +: ma.argss.argssList) exists (hasUndeclaredBVs0(_, declared))
          case _ => false
        }

        hasUndeclaredBVs0(r, Set.empty)
      }

      def extendFunc(args: List[Rep], maybeFunc: Option[Func]): Option[Func] = {
        val xteeifiedArgs = args.map(arg => replaceBVs(arg)(bv => es.ctx.getOrElse(bv, bv)))
        
        println(s"ARGS0: $xteeifiedArgs")
        
        val hopArgs = args.map(arg => bindVal("hopArg", arg.typ, Nil))
        
        val transformations = xteeifiedArgs zip hopArgs
        
        println(s"Transformation: $transformations")
        
        val after = for {
          f <- maybeFunc
          _ = println(s"BEFORE $f")
          body0 = transformations.foldLeft(fbody(f)) {
            case (body, (bv: BoundVal, hopArg)) => 
              println("bv")
              replaceBVs(body){ bv0 => if (bv0 == bv) hopArg else bv0 } alsoApply (res => println(s"BLA $res"))
            case (body, (xtor, hopArg)) => rewriteRep0(xtor, body, _ => Some(hopArg))(true)(State.forRewriting(xtor, body)) getOrElse body
          }
          _ = println(s"PASSED $body0")
          invCtx = reverse(es.ctx)
          _ = println(s"INVCTX: $invCtx")
          _ = println(s"VISIBLE: $visible")
          _ = bottomUpPartial(body0) { case bv: BoundVal if visible contains bv => return None }
          _ = println("OOPS")
        } yield (hopArgs :: fargss(f)) -> body0
        
        println(s"AFTER: $after")
        
        after
      }
      
      es.updateExtractWith(
        typ extract (xtee.typ, Covariant),
        for {
          f <- argss.foldRight(Option(emptyFunc(xtee)))(extendFunc)
          _ = println(s"F: $f")
          l = fargss(f).foldRight(fbody(f)) { case (args, body) => wrapConstruct(lambda(args, body)) }
          if !hasUndeclaredBVs(l)
          _ = println(s"GOT THORUGHT")
        } yield repExtract(name -> l)
      )
    }

    def extractLBs(lb1: LetBinding, lb2: LetBinding)(implicit es: State): ExtractState = (effect(lb1.value), effect(lb2.value)) match {
      case (Impure, Impure) =>
        extractDefs(lb1.value, lb2.value) match {
          case Right(es) =>
            //if (es.makeUnreachable) lb2.isUnreachable = true
            extractWithState(lb1.body, lb2.body)(es withCtx lb1.bound -> lb2.bound withMatchedImpures lb2.bound)
          case Left(es) => Left(es withFailed lb1.bound -> lb2.bound)
        }
        
      case (Pure, Pure) => (es.mks.xtorMarker(lb1.bound), es.mks.xteeMarker(lb2.bound)) match {
        case (EndPoint, EndPoint) =>
          extractWithState(lb1.bound, lb2.bound) match {
            case Right(es) =>
              extractWithState(lb1.body, lb2.body)(es withoutMarkers(lb1.bound, lb2.bound)) // withMatched lb2.bound)
            case Left(es) => extractWithState(lb1, lb2.body)(es)
          }
        case (EndPoint, NonEndPoint) => extractWithState(lb1, lb2.body)
        case (NonEndPoint, EndPoint) => extractWithState(lb1.body, lb2)
        case (NonEndPoint, NonEndPoint) => extractWithState(lb1.body, lb2.body)
      }

      case (Impure, Pure) => extractWithState(lb1, lb2.body)
      case (Pure, Impure) => extractWithState(lb1.body, lb2)
    }

    def extractHole(h: Hole, r: Rep)(implicit es: State): ExtractState = {
      println(s"ExtractHole: $h --> $r")
      
      //def makeUnreachable(r: Rep): Rep = r match {
      //  case lb: LetBinding => 
      //    //lb.isUnreachable = true
      //    makeUnreachable(lb.body)
      //  case _ => r
      //}
      
      (h, r) match {
        case (Hole(n, t), bv: BoundVal) =>
          es.updateExtractWith(
            t extract (xtee.typ, Covariant), 
            Some(repExtract(n -> bv))
          ).map(_ withMatchedImpures bv)

        case (Hole(n, t), lb: LetBinding) =>
          es.updateExtractWith(
            t extract (lb.typ, Covariant),
            Some(repExtract(n -> wrapConstruct(letbind(lb.value))))
          ).map {
            //makeUnreachable(lb)
            _ withMatchedImpures lb 
          }

        case (Hole(n, t), _) =>
          es.updateExtractWith(
            t extract(xtee.typ, Covariant),
            Some(repExtract(n -> xtee))
          )
      }
    }

    def extractInside(bv: BoundVal, d: Def)(implicit es: State): ExtractState = {
      def bvs(d: Def): List[BoundVal] = d match {
        case ma: MethodApp => (ma.self :: ma.argss.argssList).foldRight(List.empty[BoundVal]) {
          case (bv: BoundVal, acc) => bv :: acc
          case (_, acc) => acc
        }
        case _ => Nil
      }

      bvs(d).foldLeft[ExtractState](Left(es)) { case (acc, bv2) => 
        for {
          es1 <- acc.left
          es2 <- extractWithState(bv, bv2)(es1).left
        } yield es2
      } alsoApply (s => println(s"FOO: $s"))
    }

    def contentsOf(h: Hole)(implicit es: State): Option[Rep] = es.ex._1 get h.name // TODO check in ex._3, return Option[List[Rep]]

    println(s"extractWithState: $xtor\n$xtee\n")
    xtor -> xtee match {
      case (h: Hole, lb: LetBinding) => contentsOf(h) match {
        case Some(lb1: LetBinding) if lb1.value == lb.value => Right(es)
        case Some(_) => Left(es)
        case None => extractHole(h, xtee)
      }

      case (h: Hole, _) => contentsOf(h) match {
        case Some(`xtee`) => Right(es)
        case Some(_) => Left(es)
        case None => extractHole(h, xtee)
      }

      case (HOPHole2(name, typ, argss, visible), _) => extractHOPHole(name, typ, argss, visible)

      case (lb1: LetBinding, lb2: LetBinding) => extractLBs(lb1, lb2)

      // Stop at markers?  
      case (lb: LetBinding, _: Rep) => (effect(lb), effect(xtee)) match {
        case (Pure, Pure) => extractWithState(lb.body, xtee)
        case (Impure, Pure) => Left(es)
        case (_, Impure) => Left(es) // Assuming the return value cannot be impure
      }
        
      case (bv: BoundVal, lb: LetBinding) => 
        println("TRING")
        for {
          es1 <- extractWithState(bv, lb.bound).left
          es2 <- extractInside(bv, lb.value)(es1).left
          es3 <- extractWithState(bv, lb.body)(es2).left
        } yield es3

      case (_: Rep, lb: LetBinding) if es.matchedImpureBVs contains lb.bound => extractWithState(xtor, lb.body)
      //case (_: Rep, lb: LetBinding) if es.matchedBVs contains lb.bound => extractWithState(xtor, lb.body)

      case (_, Ascribe(s, _)) => extractWithState(xtor, s)

      case (Ascribe(s, t), _) => for {
        es1 <- es.updateExtractWith(t extract(xtee.typ, Covariant))
        es2 <- extractWithState(s, xtee)(es1)
      } yield es2

      case (HOPHole(name, typ, argss, visible), _) => extractHOPHole(name, typ, argss, visible)

      case (bv1: BoundVal, bv2: BoundVal) =>
        println(s"EXTRACTIONSTATE IN BV: $es")
        println(s"OWNERS: ${bv1.owner} -- ${bv2.owner}")
        if (es.ctx.getOrElse(bv1, bv1) == bv2) Right(es)
        else if (es.failedMatches(bv1) contains bv2) Left(es)
        else (bv1.owner, bv2.owner) match {
          case (lb1: LetBinding, lb2: LetBinding) => extractDefs(lb1.value, lb2.value) match {
            case Right(es) =>
              //if (es.makeUnreachable) lb2.isUnreachable = true
              Right(es withCtx lb1.bound -> lb2.bound withMatchedImpures lb2.bound)
            case Left(es) => Left(es withFailed lb1.bound -> lb2.bound)
          }
          case (l1: Lambda, l2: Lambda) => extractDefs(l1, l2) map (_ withCtx l1.bound -> l2.bound) // TODO handle failed extract?
          case _ => Left(es withFailed bv1 -> bv2)
        }

      case (Constant(v1), Constant(v2)) if v1 == v2 => es updateExtractWith (xtor.typ extract(xtee.typ, Covariant))

      // Assuming if they have the same name the type is the same
      case (StaticModule(fn1), StaticModule(fn2)) if fn1 == fn2 => Right(es)

      // Assuming if they have the same name and prefix the type is the same
      case (Module(p1, n1, _), Module(p2, n2, _)) if n1 == n2 => extractWithState(p1, p2)

      case (NewObject(t1), NewObject(t2)) => es updateExtractWith (t1 extract(t2, Covariant))

      case _ => Left(es)
    }
  } alsoApply (res => println(s"Extract: $res"))
  
  protected def spliceExtract(xtor: Rep, args: Args): Option[Extract] = xtor match {
    // Should check that type matches, but don't see how to access it for Args
    case SplicedHole(n, _) => Some(Map(), Map(), Map(n -> args.reps))

    case Hole(n, t) =>
      val rep = methodApp(
        staticModule("scala.collection.Seq"),
        loadMtdSymbol(
          loadTypSymbol("scala.collection.generic.GenericCompanion"),
          "apply",
          None),
        List(t),
        List(Args()(args.reps: _*)),
        staticTypeApp(loadTypSymbol("scala.collection.Seq"), List(t)))
      Some(repExtract(n -> rep))

    case _ => throw IRException(s"Trying to splice-extract with invalid extractor $xtor")
  }

  def extractDefs(v1: Def, v2: Def)(implicit es: State): ExtractState = {
    println(s"VALUES: \n\t$v1\n\t$v2 with $es \n\n")
    (v1, v2) match {
      case (l1: Lambda, l2: Lambda) =>
        for {
          es1 <- es updateExtractWith (l1.boundType extract(l2.boundType, Covariant))
          es2 <- extractWithState(l1.body, l2.body)(es1 withCtx l1.bound -> l2.bound)
        } yield es2

      case (ma1: MethodApp, ma2: MethodApp) if ma1.mtd == ma2.mtd =>
        def targExtract(es0: State): ExtractState =
          es0.updateExtractWith(
            (for {
              (e1, e2) <- ma1.targs zip ma2.targs
            } yield e1 extract(e2, Invariant)): _*
          )

        def extractArgss(argss1: ArgumentLists, argss2: ArgumentLists)(implicit es: State): ExtractState = {
          def extractArgss0(argss1: ArgumentLists, argss2: ArgumentLists, acc: List[Rep])(implicit es: State): ExtractState = (argss1, argss2) match {
            case (ArgumentListCons(h1, t1), ArgumentListCons(h2, t2)) => for {
              es0 <- extractArgss0(h1, h2, acc)
              es1 <- extractArgss0(t1, t2, acc)(es0)
            } yield es1

            case (ArgumentCons(h1, t1), ArgumentCons(h2, t2)) => for {
              es0 <- extractArgss0(h1, h2, acc)
              es1 <- extractArgss0(t1, t2, acc)(es0)
            } yield es1

            case (SplicedArgument(arg1), SplicedArgument(arg2)) => extractWithState(arg1, arg2)
            case (sa: SplicedArgument, ArgumentCons(h, t)) => extractArgss0(sa, t, h :: acc)
            case (sa: SplicedArgument, r: Rep) => extractArgss0(sa, NoArguments, r :: acc)
            case (SplicedArgument(arg), NoArguments) => es updateExtractWith spliceExtract(arg, Args(acc.reverse: _*))
            case (r1: Rep, r2: Rep) => extractWithState(r1, r2)
            case (NoArguments, NoArguments) => Right(es)
            case (NoArgumentLists, NoArgumentLists) => Right(es)
            case _ => Left(es)
          }

          extractArgss0(argss1, argss2, Nil)
        }

        for {
          es1 <- extractWithState(ma1.self, ma2.self)
          es2 <- targExtract(es1)
          es3 <- extractArgss(ma1.argss, ma2.argss)(es2)
          es4 <- es3.updateExtractWith(ma1.typ extract (ma2.typ, Covariant))
        } yield es4

      case (DefHole(h), _) => extractWithState(h, wrapConstruct(letbind(v2)))

      case _ => Left(es)
    }
  }
  
  override def rewriteRep(xtor: Rep, xtee: Rep, code: Extract => Option[Rep]): Option[Rep] = {
    println(s"Again")
    rewriteRep0(xtor, xtee, code)(false)(State.forRewriting(xtor, xtee))
  }

  def rewriteRep0(xtor: Rep, xtee: Rep, code: Extract => Option[Rep])(internalRec: Boolean)(implicit es: State): Option[Rep] = {
    def rewriteRepWithState(xtor: Rep, xtee: Rep)(implicit es: State): ExtractState = {
      println(s"rewriteRepWithState(\n\t$xtor\n\t$xtee)($es)")

      (xtor, xtee) match {
        case (lb1: LetBinding, lb2: LetBinding) if !internalRec => ((effect(lb1.value), es.mks.xtorMarker(lb1.bound)), (effect(lb2.value), es.mks.xteeMarker(lb2.bound))) match {
          case ((Pure, NonEndPoint), (Pure, NonEndPoint)) => Left(es)
          case _ => extractWithState(lb1, lb2) // TODO With unreachable handling TODO why did I mean?
        }
        case _ => extractWithState(xtor, xtee)
      }
    }

    def genCode(implicit es: State): Option[Rep] = {
      def preCheck(ex: Extract): Boolean = {
        def preCheckRep(declaredBVs: Set[BoundVal], invCtx: Map[BoundVal, Set[BoundVal]], r: Rep): Boolean = {
          def preCheckDef(declaredBVs: Set[BoundVal], invCtx: Map[BoundVal, Set[BoundVal]], d: Def): Boolean = {
            d match {
              case l: Lambda => preCheckRep(declaredBVs, invCtx, l.body)
              case ma: MethodApp => (ma.self :: ma.argss.argssList) forall {
                case bv: BoundVal =>
                  (declaredBVs contains bv) ||
                    ((for {
                      bvs <- invCtx.get(bv)
                      isUserDefined = bvs map (_.owner) forall {
                        case lb: LetBinding => lb.isUserDefined
                        case _ => true
                      }
                    } yield isUserDefined) getOrElse false)
                case lb: LetBinding => preCheckRep(declaredBVs, invCtx, lb)
                case _ => true
              }
              case _ => true
            }
          }

          r match {
            case lb: LetBinding =>
              val acc0 = declaredBVs + lb.bound
              preCheckDef(acc0, invCtx, lb.value) && preCheckRep(acc0, invCtx, lb.body)
            case _ => true
          }
        }

        val invCtx = reverse(es.ctx)
        (ex._1.values ++ ex._3.values.flatten).forall(preCheckRep(Set.empty, invCtx, _))
      }

      def check(declaredBVs: Set[BoundVal], matchedImpureBVs: Set[BoundVal])(r: Rep): Boolean = {
        def checkDef(declaredBVs: Set[BoundVal], matchedBVs: Set[BoundVal])(d: Def): Boolean = d match {
          case ma: MethodApp => (ma.self :: ma.argss.argssList) forall {
            case bv: BoundVal => (declaredBVs contains bv) || !(matchedBVs contains bv)
            case lb: LetBinding => check(declaredBVs + lb.bound, matchedBVs)(lb)
            case _ => true
          }
          case l: Lambda => 
            ((declaredBVs contains l.bound) || 
            !(matchedBVs contains l.bound)) && 
              check(declaredBVs, matchedBVs)(l.body)
          case _ => true
        }

        r match {
          case lb: LetBinding => checkDef(declaredBVs + lb.bound, matchedImpureBVs)(lb.value)
          case bv: BoundVal => (declaredBVs contains bv) || !(matchedImpureBVs contains bv)
          case _ => true
        }
      }


      def cleanup(r: Rep)(implicit es: State): Rep = r match {
        case lb: LetBinding if es.matchedImpureBVs contains lb.bound => cleanup(lb.body)
        case lb: LetBinding =>
          lb.body = cleanup(lb.body)
          lb
        case _ => r
      }
      
      if (preCheck(es.ex) alsoApply println)
        for {
          code <- code(es.ex)
          _ = println(code)
          if check(Set.empty, es.matchedImpureBVs)(cleanup(code) alsoApply println) alsoApply println
        } yield code
      else None
    }
    
    rewriteRepWithState(xtor, xtee) match {
      case Right(es) => genCode(es) alsoApply println
      case Left(_) => None
    }
  }
  
  // * --- * --- * --- *  Implementations of `QuasiBase` methods  * --- * --- * --- *

  def hole(name: String, typ: TypeRep) = Hole(name, typ)
  def splicedHole(name: String, typ: TypeRep): Rep = SplicedHole(name, typ)
  def typeHole(name: String): TypeRep = DummyTypeRep
  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]) = HOPHole(name, typ, yes, no)
  override def hopHole2(name: String, typ: TypeRep, args: List[List[Rep]], visible: List[BoundVal]) =
    HOPHole2(name, typ, args, visible filterNot (args.flatten contains _))
  def substitute(r: => Rep, defs: Map[String, Rep]): Rep = {
    println(s"Subs: $r with $defs")
    if (defs isEmpty) r |> inlineBlock // TODO works if I remove this...
    else bottomUp(r) {
      case h@Hole(n, _) => defs getOrElse(n, h)
      case h@SplicedHole(n, _) => defs getOrElse(n, h)
      //case h: BoundVal => defs getOrElse(h.name, h) // TODO FVs in lambda become BVs too early, this should be changed!!
      case h => h
    } |> inlineBlock
  }


  // * --- * --- * --- *  Implementations of `TypingBase` methods  * --- * --- * --- *
  
  import scala.reflect.runtime.universe.TypeTag // TODO do without this

  def uninterpretedType[A: TypeTag]: TypeRep = DummyTypeRep
  def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = DummyTypeRep
  def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = DummyTypeRep //unsupported
  def recordType(fields: List[(String, TypeRep)]): TypeRep = DummyTypeRep
  def constType(value: Any, underlying: TypeRep): TypeRep = DummyTypeRep

  def typLeq(a: TypeRep, b: TypeRep): Boolean = true

  def loadTypSymbol(fullName: String): TypSymbol = new TypeSymbol(fullName) // TODO


  // * --- * --- * --- *  Misc  * --- * --- * --- *
  
  def unsupported = lastWords("This part of the IR is not yet implemented/supported")
  
  override def showRep(r: Rep) = r.toString // TODO impl pretty-printing
  
  val FunApp = `scala.Function1`.`method apply`.value
  
}

class ReificationContext(val inExtractor: Bool) { reif =>
  var firstLet: FlatOpt[LetBinding] = Non
  var curLet: FlatOpt[LetBinding] = Non
  def += (lb: LetBinding): Unit = {
    curLet match {
      case Non => firstLet = lb.som
      case Som(cl) => cl.body = lb
    }
    curLet = lb.som
  }
  def += (d: Def): Symbol = new Symbol {
    protected var _parent: SymbolParent = new LetBinding("tmp", this, d, this) alsoApply (reif += _)
  }
  def finalize(r: Rep) = {
    firstLet match {
      case Non => 
        assert(curLet.isEmpty)
        r
      case Som(fl) =>
        curLet.get.body = r
        fl
    }
  }
}
