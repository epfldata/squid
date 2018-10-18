package squid.ir
package graph

import squid.utils._
import squid.utils.CollectionUtils.MutSetHelper
import squid.utils.meta.{RuntimeUniverseHelpers => ruh}

import scala.collection.mutable

trait GraphRewriting extends AST { graph: Graph =>
  
  override def mapDef(f: Def => Def)(r: Rep) = {
    val d = r.dfn
    val newD = f(d)
    //println(s"..mapD $d>$newD")
    rebind(r, newD)
  }
  override protected def mapRep(rec: Rep => Rep)(d: Def) = d match {
    case Arg(cid,cbr,els) =>
      val cbr2 = rec(cbr)
      val els2 = rec(els)
      //println(s"..mapR $cbr>$cbr2 $els>$els2")
      if ((cbr2 eq cbr) && (els2 eq els)) d
      else Arg(cid,cbr2,els2)
    case Call(cid,res) =>
      val res2 = rec(res)
      if (res2 eq res) d
      else Call(cid,res2)
    case _ => super.mapRep(rec)(d)
  }
  //protected def mapRep_!(rec: Rep => Rep) = {
  //  val f = mapRep{ r => val r2 = rec(r); if (r neq r2)  }
  //  (d: Def) =>
  //}
  
  //override def extractVal(r: Rep) = Some(r.bound)
  override def extractVal(r: Rep) = super.extractVal(r)//.orElse(Some(r.bound))
  
  //import squid.lib.MutVar
  //type XCtx = (Set[CallId],Set[CallId],MutVar[(Rep,Rep) => Rep],MutVar[List[Rep]])
  //def newXCtx: XCtx = (Set.empty,Set.empty,MutVar((r,_)=>r),MutVar(Nil))
  def newXCtx: XCtx = ??? // we don't use the inherited matching mechanism anymore
  
  
  /* TODOlater make transformed a weak hashmap with the Rep xtor as the key... or even just a weak hash set? */
  protected val transformed = mutable.Set.empty[(Rep,List[Rep])]
  def alreadyTransformedBy(xtor: Rep, ge: GraphExtract): Bool = transformed contains ((xtor, ge.traversedReps)) //alsoDo println(transformed.size)
  def rememberTransformedBy(xtor: Rep, ge: GraphExtract): Unit = transformed += ((xtor, ge.traversedReps))
  /* // weak map with first traversed Rep as key – doesn't make a huge difference...
  protected val transformed = new java.util.WeakHashMap[Rep,mutable.Set[(Rep,List[Rep])]]()
  def alreadyTransformedBy(xtor: Rep, ge: GraphExtract): Bool =
    //println(transformed.size()) thenReturn 
    transformed.containsKey(ge.traversedReps.head) && transformed.get(ge.traversedReps.head)(xtor, ge.traversedReps)
  def rememberTransformedBy(xtor: Rep, ge: GraphExtract): Unit = {
    val hd = ge.traversedReps.head
    val set = if (!transformed.containsKey(hd)) mutable.Set.empty[(Rep,List[Rep])] also (transformed.put(hd,_)) else transformed.get(hd)
    set += ((xtor, ge.traversedReps))
  }
  */
  /* // -- Alternative: also storing the traversed cids:
  protected val transformed = mutable.Set.empty[(Rep,Set[CallId],Set[CallId],List[Rep])]
  def alreadyTransformedBy(xtor: Rep, ge: GraphExtract): Bool = transformed contains ((xtor, ge.argsToRebuild, ge.callsToAvoid, ge.traversedReps))
  def rememberTransformedBy(xtor: Rep, ge: GraphExtract): Unit = transformed += ((xtor, ge.argsToRebuild, ge.callsToAvoid, ge.traversedReps))
  */
  
  override def spliceExtract(xtor: Rep, args: Args)(implicit ctx: XCtx) = ??? // TODO
  override def extract(xtor: Rep, xtee: Rep)(implicit ctx: XCtx) =
    extractGraph(xtor,xtee)(GXCtx mk false).headOption map (_.extr)
  
  override def rewriteRep(xtor: Rep, xtee: Rep, code: Extract => Option[Rep]): Option[Rep] = {
    
    val matches = extractGraph(xtor, xtee, extractTopLevelCallArg = false)(GXCtx mk true) flatMap
      (_ merge (GraphExtract fromExtract repExtract(SCRUTINEE_KEY -> xtee)))
    
    //println(matches.map(ge => "\n"+(if (alreadyTransformedBy(xtor,ge)) "✗ " else "√ ")+ge).mkString)
    //if (matches.nonEmpty) println(s"Matches at ${xtor.bound} : ${matches.count(alreadyTransformedBy(xtor,_))} / ${matches.size}")
    
    matches.filterNot(alreadyTransformedBy(xtor,_)).flatMap { ge =>
      //println(s"...considering $xtor << ${ge.traversedReps.map(_.simpleString)} --> ${ge.extr}")
      //println(s"...  ${ge.argsToRebuild} ${ge.callsToAvoid}")
      code(ge.extr) |>? {
        case Some(x0) =>
          println(s"...transforming ${xtor.simpleString} << ${ge.traversedReps.map(_.simpleString)}")
          println(s"...  ${ge.argsToRebuild} ${ge.callsToAvoid}")
          assert(!(ge.argsToRebuild intersects ge.callsToAvoid), s"${ge.argsToRebuild }>< ${ge.callsToAvoid}")
          val x = rebuild(x0, ge.argsToRebuild.toList, xtee)
          //val x = rebuild(x0, (ge.argsToRebuild--ge.callsToAvoid).toList, xtee)
          rememberTransformedBy(xtor,ge)
          x
      }
    }.headOption
    
  }
  protected[graph] def rebuild(rep: Rep, cids: List[CallId], fallBack: Rep): Rep = cids match {
    case cid :: cids => Arg(cid,rebuild(rep,cids,Call(cid,fallBack).toRep),fallBack).toRep
    case Nil => rep
  }
  
  protected case class GraphExtract(extr: Extract, traversedReps: List[Rep], argsToRebuild: Set[CallId], callsToAvoid: Set[CallId]) {
    //assert(!(argsToRebuild intersects callsToAvoid), s"$argsToRebuild >< $callsToAvoid")  // apparently not always true
    def merge(that: GraphExtract): Stream[GraphExtract] =
      if ((argsToRebuild intersects that.callsToAvoid) || (that.argsToRebuild intersects callsToAvoid)) Stream.Empty
      else graph.merge(extr,that.extr).map(e =>
        GraphExtract(e, traversedReps ++ that.traversedReps, argsToRebuild ++ that.argsToRebuild, callsToAvoid ++ that.callsToAvoid)).toStream
    def matching (r: Rep) = r.dfn match {
      case sv: SyntheticVal => this
      case _ => copy(traversedReps = r :: traversedReps)
    }
    override def toString = s"{${argsToRebuild.mkString(",")}}\\{${callsToAvoid.mkString(",")}} \t${extr._1(SCRUTINEE_KEY)} ${
      (extr._1-SCRUTINEE_KEY).map(r => "\n\t "+r._1+" -> "+r._2).mkString}"
  }
  protected object GraphExtract {
    val Empty: GraphExtract = GraphExtract(EmptyExtract, Nil, Set.empty, Set.empty)
    def fromExtract(e: Extract): GraphExtract = Empty copy (extr = e)
  } 
  protected def streamSingle[A](a: A): Stream[A] = a #:: Stream.Empty
  
  protected case class GXCtx(assumedCalled: Set[CallId], assumedNotCalled: Set[CallId], curCalls: Set[CallId], valMap: Map[Val,Val], traverseArgs: Bool)
  protected object GXCtx { def mk(traverseArgs: Bool) = GXCtx(Set.empty,Set.empty,Set.empty,Map.empty,traverseArgs) }
  
  /*
  // needs to prevent loops!
  protected def removeArgs(avoidedCalls: Set[CallId])(rep: Rep): Rep = {
    val rec = removeArgs(avoidedCalls) _
    // don't rebuild if didn't change! try to conserve reference/binder equality
    rep.dfn match {
      case Arg(cid,cbr,els) if avoidedCalls contains cid => removeArgs(avoidedCalls-cid)(els) // Q: correct to remove cid?
      case Arg(cid,cbr,els) => Arg(cid,cbr|>rec,els|>rec).toRep
      //case Call(cid,res) => Call(cid,res|>rec).toRep // Q: correct?
      case Call(cid,res) => Call(cid,res|>removeArgs(avoidedCalls-cid)).toRep // Q: correct?
      case Abs(p,b) => abs(p,b|>rec)
      case bd: BasicDef => bd.rebuild(bd.reps map rec).toRep
    }
  } //also (res => println(s"rem  $rep  -->  "+res))
  // new version, still needs prevent loops!
  protected def removeArgs(avoidedCalls: Set[CallId])(rep: Rep): Rep = {
    val transformed = mutable.Map.empty[(Rep,Set[CallId]),Rep]
    def rec(rep: Rep)(implicit avoidedCalls: Set[CallId]): Rep =
    // TODO don't rebuild if didn't change! try to conserve reference/binder equality
    transformed.getOrElseUpdate(rep->avoidedCalls, rep.dfn match {
      case Arg(cid,cbr,els) if avoidedCalls contains cid => rec(els)(avoidedCalls-cid) // Q: correct to remove cid?
      case Arg(cid,cbr,els) => Arg(cid,cbr|>rec,els|>rec).toRep
      //case Call(cid,res) => Call(cid,res|>rec).toRep // Q: correct?
      case Call(cid,res) => Call(cid,rec(res)(avoidedCalls-cid)).toRep // Q: correct?
      case Abs(p,b) => abs(p,b|>rec)
      case bd: BasicDef => bd.rebuild(bd.reps map rec).toRep
    })
    rec(rep)(avoidedCalls)
  } //also (res => println(s"rem  $rep  -->  "+res))
  */
  
  /* This naive algorithm currently potentially creates too many matching paths, and explores too many dead-ends;
   *  - One way to prune dead-ends early woudl be to thread the returned `callsToAvoid` into the next sibling arg;
   *  - I'm not sure how to avoid creating too many matching paths, beside having the user do as much GC and call/arg
   *    simplification as possible beforehand...
   *    Maybe when we split on what is actually a PassArg, we don't actually need to explore the two branches (but how
   *    to know? – we would return a token saying whether we ended up pruning paths because of the extra assumption...) */
  // Note: should not succesfully extract and merge two incompatible sibling args;
  //   for example (C0->10|20)+(C0->30|40) should not be able to successfully extract (C0->10+40)!!
  //   also, relatedly, forbid extracting (C0->10|C0->20|30) as (C0->20) since it's following an impossible branch!
  //   also, relatedly, extracted subtrees should be changed so that their semantics ignores calls we have ignored to reach them 
  /** This is an adaptation of AST#Def#extractImpl; relevant comments are still there but have been stripped here */
  protected def extractGraph(xtor: Rep, xtee: Rep,
                             extractTopLevelHole: Bool = true,
                             extractTopLevelCallArg: Bool = true
                            )(implicit ctx: GXCtx): Stream[GraphExtract] = {
    import GraphExtract.fromExtract
    
    xtor.dfn -> xtee.dfn match {
        
      case (_, Ascribe(v,tp)) => extractGraph(xtor,v)
        
      case (Ascribe(v,tp), _) =>
        for { a <- tp.extract(xtee.typ, Covariant).toStream
              b <- extractGraph(v,xtee,extractTopLevelCallArg=extractTopLevelCallArg)
              m <- fromExtract(a) merge b } yield m
        
      case (h:HOPHole, _) => ??? // TODO
        
      case (Hole(name), _) if extractTopLevelHole =>
        val directly = for {
          typE <- xtor.typ.extract(xtee.typ, Covariant).toStream
          r1 = xtee
          // Q: does ctx.assumedNotCalled ever intersect ctx.curCalls here?
          
          r2 = ctx.assumedNotCalled.foldRight(r1)(PassArg(_,_).toRep)
          //() = println(s">>>  $r2  =/=  ${try removeArgs(ctx.assumedNotCalled)(r1) catch { case e => e}}")
          //r2 = r1 |> removeArgs(ctx.assumedNotCalled)  // more brutal version; not sure if correctly implemented
          r3 = ctx.curCalls.foldRight(r2)(Call(_,_).toRep)
          
          e <- merge(typE, repExtract(name -> r3))
        } yield GraphExtract fromExtract e
        val inspecting = extractGraph(xtor,xtee,extractTopLevelHole=false)
        directly ++ inspecting
        
      case (_, Hole(_)) => Stream.Empty // Q: is this case really needed?
        
      case _ -> Call(cid, res) if extractTopLevelCallArg && !(ctx.curCalls contains cid) /*&& !(ctx.avoidedCalls contains cid)*/ =>
        extractGraph(xtor, res)(ctx.copy(curCalls = ctx.curCalls + cid))
      case _ -> Arg(cid, cbr, _) if extractTopLevelCallArg && ctx.traverseArgs && (ctx.curCalls contains cid) =>
        extractGraph(xtor, cbr)(ctx.copy(curCalls = ctx.curCalls - cid))
      case _ -> PassArg(cid, res) if extractTopLevelCallArg && (ctx.curCalls contains cid) => ??? // TODO rm traverseArgs?
      case _ -> Arg(cid, cbr, els) if extractTopLevelCallArg && ctx.traverseArgs =>
        val cbrE = if (ctx.assumedCalled contains cid) Stream.Empty else // TODO give multiplicities to curCalls/curArgs? (while making sure not to recurse infinitely...)
          extractGraph(xtor, cbr)(ctx.copy(assumedCalled = ctx.assumedCalled + cid))
        val elsE = extractGraph(xtor, els)(ctx.copy(assumedNotCalled = ctx.assumedNotCalled + cid)) // should we not do this if cid already in avoidedCalls? is it also a risk of infinite loop?
        cbrE ++ elsE
        
      case (v1: BoundVal, v2: BoundVal) =>  // TODO implement other schemes for matching variables... cf. extractImpl
        // Q: check same type?
        if (
           v1 == v2 // Q: really legit?
        || ctx.valMap.get(v1).contains(v2)
        ) EmptyExtract |> fromExtract |> streamSingle else Stream.Empty
        
      case (Constant(v1), Constant(v2)) =>
        mergeOpt(extractType(xtor.typ, xtee.typ, Covariant), if (v1 == v2) Some(EmptyExtract) else None).map(fromExtract).toStream
        
      case (a1: Abs, a2: Abs) =>
        require(a1.param.isExtractedBinder, s"alternative not implemented yet")
        for {
          pt <- a1.ptyp.extract(a2.ptyp, Contravariant).toStream //map fromExtract
          (hExtr,h) = a2.param.toHole(a1.param)
          //m <- mergeGraph(pt, hExtr |> fromExtract)
          m <- merge(pt, hExtr).toStream
          b <- extractGraph(a1.body, a2.body)(ctx.copy(valMap = ctx.valMap + (a1.param -> a2.param)))
          m <- mergeGraph(m |> fromExtract, b)
        } yield m
        
      case (StaticModule(fullName1), StaticModule(fullName2)) if fullName1 == fullName2 =>
        fromExtract(EmptyExtract) into streamSingle
        
      case Module(pref0, name0, tp0) -> Module(pref1, name1, tp1) =>
        extractGraph(pref0,pref1).flatMap(_ optionIf name0 == name1) ++ extractType(tp0,tp1,Invariant).map(fromExtract).toStream
        
      case (NewObject(tp1), NewObject(tp2)) => tp1 extract (tp2, Covariant) map fromExtract toStream
        
      case (MethodApp(self1,mtd1,targs1,args1,tp1), MethodApp(self2,mtd2,targs2,args2,tp2))
        if mtd1 === mtd2 || { debug(s"Symbol: ${mtd1.fullName} =/= ${mtd2.fullName}"); false }
      =>
        assert(args1.size == args2.size, s"Inconsistent number of argument lists for method $mtd1: $args1 and $args2")
        assert(targs1.size == targs2.size, s"Inconsistent number of type arguments for method $mtd1: $targs1 and $targs2")
        for {
          s <- extractGraph(self1,self2)
          t <- mergeAll( (targs1 zip targs2) map { case (a,b) => a extract (b, Covariant) } ).toStream
          a <- mergeAllGraph( (args1 zip args2) map { case (as,bs) => extractGraphArgList(as, bs) } )
          rt = GraphExtract fromExtract EmptyExtract
          m0 <- mergeGraph(s, GraphExtract fromExtract t)
          m1 <- mergeGraph(m0, a)
          m2 <- mergeGraph(m1, rt)
        } yield m2
        
      case (a:ConstantLike) -> (b:ConstantLike) if a.value === b.value => GraphExtract.Empty |> streamSingle
        
      case _ =>
        //println(s"Nope: ${xtor} << $xtee")
        Stream.Empty
    }
    
  }.map(_ matching xtee).map { ge =>
    ge.copy(argsToRebuild = ge.argsToRebuild ++ ctx.assumedCalled, callsToAvoid = ge.callsToAvoid ++ ctx.assumedNotCalled)
  }
  
  protected def mergeGraph(lhs: GraphExtract, rhs: GraphExtract)(implicit ctx: GXCtx): Stream[GraphExtract] = lhs merge rhs
  protected def extractGraphArgList(self: ArgList, other: ArgList)(implicit ctx: GXCtx): Stream[GraphExtract] = {
    def extractRelaxed(slf: Args, oth: Args): Stream[GraphExtract] = {
      import slf._
      if (reps.size != oth.reps.size) return Stream.Empty
      val args = (reps zip oth.reps) map { case (a,b) => extractGraph(a, b) }
      //(streamSingle(EmptyExtract |> GraphExtract.fromExtract) /: args) {
      (streamSingle(GraphExtract.Empty) /: args) {
        case (acc, a) => for (acc <- acc; a <- a; m <- acc merge a) yield m }
    }
    import self._
    (self, other) match {
      case (a0: Args, a1: Args) =>
        require(reps.size == other.reps.size)
        extractRelaxed(a0,a1)
      case (ArgsVarargs(a0, va0), ArgsVarargs(a1, va1)) => for {
        a <- extractGraphArgList(a0, a1)
        va <- extractRelaxed(va0,va1)
        m <- mergeGraph(a, va)
      } yield m
      case (ArgsVarargSpliced(a0, va0), ArgsVarargSpliced(a1, va1)) => for {
        a <- extractGraphArgList(a0, a1)
        va <- extractGraph(va0, va1)
        m <- mergeGraph(a, va)
      } yield m
      case (ArgsVarargSpliced(a0, va0), ArgsVarargs(a1, vas1)) => for { // case dsl"List($xs*)" can extract dsl"List(1,2,3)"
        a <- extractGraphArgList(a0, a1)
        va <- spliceExtractGraph(va0, vas1)
        m <- mergeGraph(a, va)
      } yield m
      case _ => Stream.Empty
    }
  }
  def spliceExtractGraph(xtor: Rep, args: Args)(implicit ctx: GXCtx): Stream[GraphExtract] = streamSingle(GraphExtract.fromExtract(xtor match {
    case RepDef(SplicedHole(name)) => mkExtract()()(name -> args.reps)
    case RepDef(h @ Hole(name)) => // If we extract ($xs*) using ($xs:_*), we have to build a Seq in the object language and return it
      mkExtract(name -> mkSeq(args.reps))()()
    case _ => throw IRException(s"Trying to splice-extract with invalid extractor $xtor")
  }))
  
  protected def mergeAllGraph(as: TraversableOnce[Stream[GraphExtract]]): Stream[GraphExtract] = {
    if (as isEmpty) return streamSingle(GraphExtract.Empty)
    val ite = as.toIterator
    var res = ite.next()
    while(ite.hasNext && res.nonEmpty) res = for { a <- res; b <- ite.next(); m <- a merge b } yield m
    res
  }
  
  override protected def unapplyConst(rep: Rep, typ: TypeRep): Option[Any] =
    unapplyConstImpl(rep,typ)(GXCtx.mk(false)) //also (r => println(s"UNAPP ${rep} -> $r"))
  
  protected def unapplyConstImpl(rep: Rep, typ: TypeRep)(implicit ctx: GXCtx): Option[Any] =
    //println(s"? $rep ${ctx.assumedCalled} ${ctx.assumedNotCalled}") thenReturn 
  rep.dfn match {
      
    case Call(c,r) 
      if !(ctx.assumedCalled contains c) // not strictly necessary, but would need multiplicities to make it sound without it... 
    => unapplyConstImpl(r,typ)(ctx.copy(assumedCalled = ctx.assumedCalled + c, assumedNotCalled = ctx.assumedNotCalled - c))
      
    case Arg(c,t,e) if ctx.assumedCalled.contains(c) => unapplyConstImpl(t,typ)(ctx.copy(assumedCalled = ctx.assumedCalled - c))
    case Arg(c,t,e) if ctx.assumedNotCalled.contains(c) => unapplyConstImpl(e,typ) // Note: c still assumed not called!
      
    case Arg(c,t,e) 
      if !(ctx.assumedNotCalled contains c) && !(ctx.assumedCalled contains c) // not strictly necessary again
    => for {
        c0 <- unapplyConstImpl(t,typ)(ctx.copy(assumedNotCalled = ctx.assumedNotCalled + c))
        c1 <- unapplyConstImpl(e,typ)(ctx.copy(assumedCalled = ctx.assumedCalled + c))
        if c0 === c1
      } yield c0
      
    // Note: it would be unsound to follow Arg branches, because it's partial (discards info)
    //case Arg(_,cbr,els) => unapplyConst(cbr,typ) orElse unapplyConst(els,typ)
      
    case _ => super.unapplyConst(rep,typ)
  }
  
}
