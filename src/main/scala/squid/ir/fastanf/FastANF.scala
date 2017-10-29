package squid
package ir.fastanf

import utils._
import lang.{Base, InspectableBase, ScalaCore}
import squid.ir.{Covariant, CurryEncoding, IRException, Invariant}

import scala.collection.immutable.ListMap

class FastANF extends InspectableBase with CurryEncoding with ScalaCore {
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
  def readVal(bv: BoundVal): Rep = bv
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
  def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = {
    MethodApp(self, mtd, targs, argss |> toArgumentLists, tp) |> letbind
  }
  def byName(mkArg: => Rep): Rep = wrapNest(mkArg)
  
  def letbind(d: Def): Rep = currentScope += d
  
  override def ascribe(self: Rep, typ: TypeRep): Rep = if (self.typ =:= typ) self else self match {
    case Ascribe(trueSelf, _) => Ascribe(trueSelf, typ) // Hopefully Scala's subtyping is transitive!
    case _ => Ascribe(self, typ)
  }

  def loadMtdSymbol(typ: TypSymbol, symName: String, index: Option[Int] = None, static: Boolean = false): MtdSymbol = new MethodSymbol(typ, symName) // TODO

  object Const extends ConstAPI {
    def unapply[T: IRType](ir: IR[T,_]): Option[T] = ir.rep match {
      case cst @ Constant(v) if typLeq(cst.typ, irTypeOf[T].rep) => Some(v.asInstanceOf[T])
      case _ => None
    }
  }

  //   /** Artifact of a term extraction: map from hole name to terms, types and spliced term lists */

  def repEq(a: Rep, b: Rep): Boolean = {
    (a extractRep b) === (b extractRep a) && (a extractRep b) === Some(EmptyExtract) && (b extractRep a) === Some(EmptyExtract)

    //val aExtractB = a extractRep b
    //
    //if (aExtractB.isEmpty) false
    //else {
    //  (aExtractB, b extractRep a) match {
    //    case (Some((xs, xts, fxs)), Some((ys, yts, fys))) =>
    //      val extractsHole: (String -> Rep) => Boolean = {
    //        case (k: String, Hole(n, _)) if k == n => true
    //        case _ => false
    //      }
    //
    //      val extractsTypeHole: (String -> TypeRep) => Boolean = {
    //        case (k: String, DummyTypeRep) => true
    //        case _ => false
    //      }
    //
    //      fxs.isEmpty && fys.isEmpty &&
    //        (xs forall extractsHole) && (ys forall extractsHole) &&
    //        (xts forall extractsTypeHole) && (yts forall extractsTypeHole)
    //    case _ => false
    //  }
    //}
  }


  // * --- * --- * --- *  Implementations of `IntermediateBase` methods  * --- * --- * --- *

  def nullValue[T: IRType]: IR[T,{}] = IR[T, {}](const(DummyTypeRep))
  def reinterpret(r: Rep, newBase: Base)(extrudedHandle: BoundVal => newBase.Rep): newBase.Rep = {
    def go: Rep => newBase.Rep = r => reinterpret(r, newBase)(extrudedHandle)
    def reinterpretType: TypeRep => newBase.TypeRep = t => newBase.staticTypeApp(newBase.loadTypSymbol("scala.Any"), Nil)
    def reinterpretBV:BoundVal => newBase.BoundVal = bv => newBase.bindVal(bv.name, reinterpretType(bv.typ), Nil)
    def reinterpretTypSym(t: TypeSymbol): newBase.TypSymbol = newBase.loadTypSymbol(t.name)
    def reinterpretMtdSym(s: MtdSymbol): newBase.MtdSymbol = newBase.loadMtdSymbol(reinterpretTypSym(s.typ), s.name)
    def reinterpretArgList(argss: ArgumentLists): List[newBase.ArgList] = toListOfArgList(argss) map {
      case ArgsVarargSpliced(args, varargs) => newBase.ArgsVarargSpliced(args.map(newBase)(go), go(varargs))
      case ArgsVarargs(args, varargs) => newBase.ArgsVarargs(args.map(newBase)(go), varargs.map(newBase)(go))
      case args : Args => args.map(newBase)(go)
    }
    def defToRep(d: Def): newBase.Rep = d match {
      case app @ App(f, a) => newBase.app(go(f), go(a))(reinterpretType(app.typ))
      case ma : MethodApp => newBase.methodApp(
        go(ma.self),
        reinterpretMtdSym(ma.mtd),
        ma.targs.map(reinterpretType),
        reinterpretArgList(ma.argss),
        reinterpretType(ma.typ))
      case l: Lambda => newBase.lambda(List(reinterpretBV(l.bound)), go(l.body))
    }

    r match {
      case Constant(v) => newBase.const(v)
      case StaticModule(fn) => newBase.staticModule(fn)
      case NewObject(t) => newBase.newObject(reinterpretType(t))
      case Hole(n, t) => newBase.hole(n, reinterpretType(t))
      case SplicedHole(n, t) => newBase.splicedHole(n, reinterpretType(t))
      case Ascribe(s, t) => newBase.ascribe(go(s), reinterpretType(t))
      case HOPHole(n, t, yes, no) => newBase.hopHole(
        n,
        reinterpretType(t),
        yes.map(_.map(reinterpretBV)),
        no.map(reinterpretBV))
      case Module(p, n, t) => newBase.module(go(p), n, reinterpretType(t))
      case lb: LetBinding => newBase.letin(
        reinterpretBV(lb.bound),
        defToRep(lb.value),
        go(lb.body),
        reinterpretType(lb.typ))
      case s: Symbol => extrudedHandle(s)
    }

  }
  def repType(r: Rep): TypeRep = r.typ
  def boundValType(bv: BoundVal) = bv.typ
  
  
  // * --- * --- * --- *  Implementations of `InspectableBase` methods  * --- * --- * --- *

  def extractType(xtor: TypeRep, xtee: TypeRep, va: squid.ir.Variance): Option[Extract] = Some(EmptyExtract) //unsupported
  def bottomUp(r: Rep)(f: Rep => Rep): Rep = transformRepAndDef(r)(identity, f)(identity)
  def topDown(r: Rep)(f: Rep => Rep): Rep = transformRepAndDef(r)(f)(identity)
  def transformRepAndDef(r: Rep)(pre: Rep => Rep, post: Rep => Rep = identity)(preDef: Def => Def, postDef: Def => Def = identity): Rep = {
    def _transformRepAndDef(r: Rep) = transformRepAndDef(r)(pre, post)(preDef, postDef)

    def transformDef(d: Def): Def = (d map preDef match {
      case App(f, a) => App(_transformRepAndDef(f), _transformRepAndDef(a))
      case ma: MethodApp => MethodApp(_transformRepAndDef(ma.self), ma.mtd, ma.targs, ma.argss map (_transformRepAndDef(_)), ma.typ)
      case l: Lambda => new Lambda(l.name, l.bound, l.boundType, _transformRepAndDef(l.body))
    }) map postDef

    (r map pre match {
      case lb: LetBinding =>
        new LetBinding(
          lb.name,
          lb.bound,
          transformDef(lb.value),
          _transformRepAndDef(lb.body)
        )
      case Ascribe(s, t) =>
        Ascribe(_transformRepAndDef(s), t)
      case Module(p, n, t) =>
        Module(_transformRepAndDef(p), n, t)
      case r @ ((_:Constant) | (_:Hole) | (_:Symbol) | (_:SplicedHole) | (_:HOPHole) | (_:NewObject) | (_:StaticModule)) => r
    }) map post
  }
  
  def transformRep(r: Rep)(pre: Rep => Rep, post: Rep => Rep = identity): Rep =
    transformRepAndDef(r)(pre, post)(identity, identity)

  protected def extract(xtor: Rep, xtee: Rep): Option[Extract] = extractWithCtx(xtor, xtee)(ListMap.empty)

  def extractWithCtx(xtor: Rep, xtee: Rep)(implicit ctx: ListMap[BoundVal, BoundVal]): Option[Extract] = xtor -> xtee match {
    case (lb1: LetBinding, lb2: LetBinding) =>
      val normal = for {
      //e1 <- extractWithCtx(lb1.bound, lb2.bound)
        e1 <- lb1.boundType extract (lb1.boundType, Covariant)
        e2 <- extractValue(lb1.value, lb2.value)
        e3 <- extractWithCtx(lb1.body, lb2.body)(ctx + (lb1.bound -> lb2.bound))
        m <- mergeAll(e1, e2, e3)
      } yield m

      /*
       * For instance when:
       * xtor: val x0 = List(Hole(...): _*)
       * xtee: val x0 = Seq(1, 2, 3); val x1 = List(x0)
       */
      // TODO CHECK CTX
      lazy val lookFurtherInXtee = extractWithCtx(lb1, lb2.body)(ctx + (lb1.bound -> lb2.bound))
      lazy val lookFurtherInXtor = extractWithCtx(lb1.body, lb2)(ctx + (lb1.bound -> lb2.bound))

      normal //orElse lookFurtherInXtee orElse lookFurtherInXtor

    // Matches 42 and 42: Any, is it safe to ignore the typ?
    case (_, Ascribe(s, _)) => extractWithCtx(xtor, s)

    case (Ascribe(s, t) , _) =>
      for {
        e1 <- t extract (xtee.typ, Covariant) // t <:< a.typ, which one to use?
        e2 <- extractWithCtx(s, xtee)
        m <- merge(e1, e2)
      } yield m

    case (Hole(n, t), _) =>
      for {
        e <- t extract (xtee.typ, Covariant)
        m <- merge(e, repExtract(n -> xtee))
      } yield m

    case (HOPHole(name, typ, args, visible), _) => unsupported

    case (bv1: BoundVal, bv2: BoundVal) =>
      if (bv1 == bv2) Some(EmptyExtract)
      else for {
        candidate <- ctx.get(bv1)
        if candidate == bv2
      } yield EmptyExtract

    case (Constant(v1), Constant(v2)) if v1 == v2 =>
      xtor.typ extract (xtee.typ, Covariant)

    // Assuming if they have the same name the type is the same
    case (StaticModule(fn1), StaticModule(fn2)) if fn1 == fn2 => Some(EmptyExtract)

    // Assuming if they have the same name and prefix the type is the same
    case (Module(p1, n1, _), Module(p2, n2, _)) if n1 == n2 => extractWithCtx(p1, p2)

    case (NewObject(t1), NewObject(t2)) => t1 extract (t2, Covariant)

    case _ => None
  }
  
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

  override def rewriteRep(xtor: Rep, xtee: Rep, code: Extract => Option[Rep]): Option[Rep] = {
    def go(ex: Extract, matchedBVs: Set[BoundVal])(_xtor: Rep, _xtee: Rep)(implicit ctx: ListMap[BoundVal, BoundVal]): Option[Rep] = {
      println(s"XTEE ->> ${_xtee}")

      def checkRefs(r: Rep): Option[Rep] = {
        def refs(r: Rep): Set[BoundVal] = {
          def bvsUsed(value: Def): Set[BoundVal] = value match {
            case ma: MethodApp =>
              def bvsInArgss(argss: ArgumentLists): Set[BoundVal] = {
                def go(argss: ArgumentLists, acc: Set[BoundVal]): Set[BoundVal] = argss match {
                  case ArgumentListCons(h, t) => go(t, go(h, acc))
                  case ArgumentCons(h, t) => go(t, go(h, acc))
                  case SplicedArgument(bv: BoundVal) => acc + bv
                  case bv: BoundVal => acc + bv
                  case _ => acc
                }

                go(argss, Set.empty)
              }

              val selfBV = ma.self match {
                case bv: BoundVal => Set(bv)
                case _ => Set.empty
              }

              selfBV ++ bvsInArgss(ma.argss)

            case l: Lambda =>
              val bodyBV: Set[BoundVal] = l.body match {
                case bv: BoundVal => Set(bv)
                case _ => Set.empty
              }

              bodyBV + l.bound
          }


          r match {
            case lb: LetBinding => bvsUsed(lb.value) ++ refs(lb.body)
            case bv: BoundVal => Set(bv)
            case _ => Set.empty
          }
        }

        if ((refs(r) & matchedBVs).isEmpty) Some(r) else None
      }

      def mkCode(e: Extract): Option[Rep] = {
        for {
          c <- code(e)
          c <- checkRefs(c)
        } yield c
      }

      def letIn(body: Rep)(xBV: BoundVal, newX: Rep): Rep = {
        println(s"----- In $body replacing $xBV with $newX")
        def findAndReplace(argss: ArgumentLists, r: BoundVal, newR: BoundVal): ArgumentLists = argss.map {
          case a if a == r => println(s"### $a -> $newR"); newR
          case a => println(s"+++ $a"); a
        }

        // In `body` replace every occurrence of `x` with `outerLB`
        def _letIn(body: Rep)(xBV: BoundVal, outerLB: LetBinding): Rep = {
          def replaceInValue(v: Def): Def = {
            v match {
              case ma: MethodApp =>
                println(s"@@@@ $ma")
                MethodApp(
                  if (ma.self == xBV) outerLB.bound else ma.self,
                  ma.mtd,
                  ma.targs,
                  findAndReplace(ma.argss, xBV, outerLB.bound),
                  ma.typ)
              case l: Lambda =>
                new Lambda(l.name,
                  l.bound,
                  l.boundType,
                  _letIn(l.body)(xBV, outerLB))
            }
          }

          body match {
            case lb: LetBinding if lb.bound == xBV => new LetBinding(outerLB.name, outerLB.bound, outerLB.value, _letIn(lb.body)(xBV, outerLB))

            case lb: LetBinding =>
              new LetBinding(
                lb.name,
                lb.bound,
                replaceInValue(lb.value),
                _letIn(lb.body)(xBV, outerLB))

            case `xBV` => outerLB.bound
            case _ => body
          }
        }

        newX match {
          case outerLB: LetBinding =>
            //xBV rebind outerLB.bound
            //body
            _letIn(removeBVs(body, matchedBVs - xBV))(xBV, outerLB) alsoApply println

          case bv: BoundVal =>
            xBV rebind bv
            body

          case _ => ??? //_letIn(removeBVs(body, matchedBVs - xBV))(xBV, newX)
        }
      }

      def withBV(r: Rep)(f: LetBinding => Option[Extract]): Option[Extract -> BoundVal] = {
//        def extractArgss(f: A => Option[Extract])(argss: ArgumentLists): Option[Extract -> BoundVal] = argss match {
//          case ArgumentListCons(h, t) => extractArgss(f)(h) orElse extractArgss(f)(t)
//          case ArgumentCons(h, t) => extractArgss(f)(h) orElse extractArgss(f)(t)
//          case SplicedArgument(a) => withBV(f)(a)
//          case r: Rep => withBV(f)(r)
//          case NoArguments | NoArgumentLists => None
//        }

        r match {
          case lb: LetBinding =>
            f(lb) map { _ -> lb.bound} orElse {
              lb.value match {
                case l: Lambda => withBV(l.body)(f)
                case _ => None
              }
            } orElse withBV(lb.body)(f)

          case _ => None
        }
      }

      def extractValueWithBV(v: Def, r: Rep): Option[Extract -> BoundVal] = withBV(r) { lb => extractValue(v, lb.value) }
      def extractBVWithBV(bv: BoundVal, r: Rep): Option[Extract -> BoundVal] = withBV(r) { lb => extractWithCtx(bv, lb.bound) }

      def removeBVs(r: Rep, bvs: Set[BoundVal]): Rep = {
        def lambdaRemove(l: Lambda): Def = {
          // TODO check l.bound?
          new Lambda(l.name, l.bound, l.boundType, removeBVs(l.body, bvs))
        }

        r match {
          case lb: LetBinding if bvs contains lb.bound => lb.body
          case lb: LetBinding => lb.value match {
            case l: Lambda => new LetBinding(lb.name, lb.bound, lambdaRemove(l), removeBVs(lb.body, bvs))
            case _ => new LetBinding(lb.name, lb.bound, lb.value, removeBVs(lb.body, bvs))
          }
          case _ => r
        }
      }

      (_xtor, _xtee) match {
        case (lb1: LetBinding, lb2: LetBinding) =>
          for {
            (e, matchedBV) <- extractValueWithBV(lb1.value, lb2)
            _ = println(s"----- Matched $matchedBV")
            if !(matchedBVs contains matchedBV) // Cannot match twice the same code line
            m <- merge(e, ex)
            r <- go(m, matchedBVs + matchedBV)(lb1.body, lb2)(ctx + (lb1.bound -> matchedBV))
          } yield r

        // Match return of `xtor` with something in `xtee`
        case (bv: BoundVal, lb: LetBinding) =>
          println(s"Knowing: $ctx")
          println(s"Matching... $bv in $lb")
          for {
            (e, matchedBV) <- extractBVWithBV(bv, lb)
            _ = println(s"----->> Matched $matchedBV")
            m <- merge(e, ex)
            newX <- mkCode(m)
            _ = println(s"Code => $newX")
            newC = letIn(lb)(matchedBV, newX) alsoApply (c => println(s"New code => $c"))
          } yield newC

        case (bv: BoundVal, xtee: Rep) =>
          for {
            (e, matchedBV) <- extractBVWithBV(bv, xtee)
            m <- merge(e, ex)
            newX <- mkCode(m)
            newC = letIn(xtee)(matchedBV, newX)
          } yield newC

        // Match Constant(42) with `value` of the `LetBinding`
        case (xtor: Rep, lb: LetBinding) =>
          type LazyInlined[R] = R -> List[LetBinding]
          implicit def lazyInlined[R](r: R): LazyInlined[R] = r -> List.empty
          def run(lr: LazyInlined[Rep]): Rep = lr match {
            case r -> lbs => lbs.foldLeft(r) { (acc, outerLB) => new LetBinding(outerLB.name, outerLB.bound, outerLB.value, acc) }
          }

          // Puts `acc` inside `outer`.
          def surroundWithLB(acc: LazyInlined[Rep], outer: LazyInlined[Rep]): LazyInlined[Rep] = outer match {
            case (outerLB: LetBinding, lbs) =>
              new LetBinding(outerLB.name, outerLB.bound, outerLB.value, run(acc)) -> lbs
            case _ => throw new IllegalArgumentException
          }


          def rewrite(lb: LetBinding): Option[Rep] = {
            def rewriteValue(lb: LetBinding): Option[LazyInlined[Rep]] = {
              val rewrittenValue = {
                def rewriteArgssReps(argss: ArgumentLists): Option[LazyInlined[ArgumentLists]] = {
                  def rewriteArgsReps(args: ArgumentList): Option[LazyInlined[ArgumentList]] = args match {
                    case ArgumentCons(h, t) => for {
                      (h, outerLBs) <- rewriteRep(h)
                      (t, innerLBs) <- rewriteArgsReps(t)
                    } yield ArgumentCons(h, t) -> (innerLBs ::: outerLBs)

                    case SplicedArgument(a) => rewriteRep(a) map { case arg -> lbs => SplicedArgument(arg) -> lbs }
                    case r: Rep => rewriteRep(r)
                    case NoArguments => Some(NoArguments)
                  }

                  argss match {
                    case ArgumentListCons(h, t) => for {
                      (h, outerLBs) <- rewriteArgsReps(h)
                      (t, innerLBs) <- rewriteArgssReps(t)
                    } yield ArgumentListCons(h, t) -> (innerLBs ::: outerLBs)

                    case args: ArgumentList => rewriteArgsReps(args)
                    case NoArgumentLists => Some(NoArgumentLists)
                  }
                }

                def rewriteRep(xtee: Rep) = {
                  def codeWithOuter(e: Extract) = {
                    def toLazy(r: Rep): LazyInlined[Rep] = {
                      def go(r: Rep, acc: List[LetBinding]): LazyInlined[Rep] = r match {
                        case lb: LetBinding => go(lb.body, lb :: acc)
                        case _ => r -> acc
                      }

                      go(r, List.empty)
                    }

                    mkCode(e) map toLazy
                  }

                  extractWithCtx(xtor, xtee).fold(Option(lazyInlined(xtee)))(codeWithOuter)
                }

                lb.value match {
                  case ma: MethodApp => for {
                    (self, outerLBs) <- rewriteRep(ma.self)
                    (argss, innerLBs) <- rewriteArgssReps(ma.argss)
                  } yield MethodApp(self, ma.mtd, ma.targs, argss, ma.typ) -> (innerLBs ::: outerLBs)

                  case l: Lambda => rewriteRep(l.body) map {
                    case body -> lbs => new Lambda(l.name, l.bound, l.boundType, body) -> lbs
                  }
                }
              }

              // Puts the value back into its LB
              rewrittenValue map { case value -> lbs => new LetBinding(lb.name, lb.bound, value, lb.body) -> lbs}
            }

            def go(lb: LetBinding, acc: Option[List[LazyInlined[Rep]]]): Option[List[LazyInlined[Rep]]] = lb.body match {
              case innerLB: LetBinding =>
                go(innerLB,
                  for {
                    acc <- acc
                    lb <- rewriteValue(lb)
                  } yield lb :: acc)

              case ret =>
                for {
                  acc <- acc
                  lb <- rewriteValue(lb)
                } yield lazyInlined(ret) :: lb :: acc
            }

            go(lb, Some(List.empty)) map {
              case ret :: outerLBs => run(outerLBs.foldLeft(ret)(surroundWithLB))
            }
          }

          rewrite(lb)

        // Matching return values
        case (r1: Rep, r2: Rep) =>
          for {
            e <- extractWithCtx(r1, r2)
            m <- merge(e, ex)
            c <- mkCode(m)
          } yield c
      }
    }

    go(EmptyExtract, Set.empty)(xtor, xtee)(ListMap.empty)
  }

  def extractValue(v1: Def, v2: Def)(implicit ctx: ListMap[BoundVal, BoundVal]) = (v1, v2) match {
    case (l1: Lambda, l2: Lambda) =>
      for {
        e1 <- l1.boundType extract (l2.boundType, Covariant)
        e2 <- extractWithCtx(l1.body, l2.body)(ctx + (l1.bound -> l2.bound))
        m <- merge(e1, e2)
      } yield m

    case (ma1: MethodApp, ma2: MethodApp) if ma1.mtd == ma2.mtd =>
      lazy val targExtract = mergeAll(for {
        (e1, e2) <- ma1.targs zip ma2.targs
      } yield e1 extract (e2, Invariant)) // TODO Invariant? Depends on its positions...

      def extractArgss(argss1: ArgumentLists, argss2: ArgumentLists): Option[Extract] = {
        def go(argss1: ArgumentLists, argss2: ArgumentLists, acc: List[Rep]): Option[Extract] = (argss1, argss2) match {
          case (ArgumentListCons(h1, t1), ArgumentListCons(h2, t2)) => mergeOpt(go(h1, h2, acc), go(t1, t2, acc))
          case (ArgumentCons(h1, t1), ArgumentCons(h2, t2)) => mergeOpt(go(h1, h2, acc), go(t1, t2, acc))
          case (SplicedArgument(arg1), SplicedArgument(arg2)) => extractWithCtx(arg1, arg2)
          case (sa: SplicedArgument, ArgumentCons(h, t)) => go(sa, t, h :: acc)
          case (sa: SplicedArgument, r: Rep) => go(sa, NoArguments, r :: acc)
          case (SplicedArgument(arg), NoArguments) => spliceExtract(arg, Args(acc.reverse: _*)) // Reverses list...
          case (r1: Rep, r2: Rep) => extractWithCtx(r1, r2)
          case (NoArguments, NoArguments) => Some(EmptyExtract)
          case (NoArgumentLists, NoArgumentLists) => Some(EmptyExtract)
          case _ => None
        }

        go(argss1, argss2, Nil)
      }

      for {
        e1 <- extractWithCtx(ma1.self, ma2.self)
        e2 <- targExtract
        e3 <- extractArgss(ma1.argss, ma2.argss)
        e4 <- ma1.typ extract (ma2.typ, Covariant)
        m <- mergeAll(e1, e2, e3, e4)
      } yield m

    case _ => None
  }
  
  // * --- * --- * --- *  Implementations of `QuasiBase` methods  * --- * --- * --- *

  def hole(name: String, typ: TypeRep) = Hole(name, typ)
  def splicedHole(name: String, typ: TypeRep): Rep = SplicedHole(name, typ)
  def typeHole(name: String): TypeRep = DummyTypeRep
  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]) = HOPHole(name, typ, yes, no)

  def substitute(r: => Rep, defs: Map[String, Rep]): Rep =
    if (defs isEmpty) r
    else bottomUp(r) {
      case h @ Hole(n, _) => defs getOrElse(n, h)
      case h @ SplicedHole(n, _) => defs getOrElse(n, h)
      case h => h
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

