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
package ir

import utils._
import collection.mutable

/**
  * Simplest encoding of ANF, using plain AST nodes and online renormalization via the `rep` function.
  * Also features an appropriate `rewriteRep` impl that understands ANF blocks;
  *   an efficient repr of the ANF block associated with an AST node is stored lazily in the Rep wrapper
  * 
  * TODO Needs to commute let bindings
  *   > take care that we're not binding the same BV several times! need to renew
  * 
  * TODO adapt extract/rewrite to ignore pure let-bound defs
  *   match in the middle of a "block": {{{ ir"readInt.toDouble.toInt" rewrite { case ir"readInt.toDouble" => ir"readDouble" } }}}
  *     need to make sure removed symbols are not used!
  *   blur distinction effects/bound-vals -- or make unused bound vals effects automatically
  * 
  * TODO CSE with a WeakHashMap[Set[Val],Rep] for pure exprs
  * 
  * TODO use a specialized Def for Imperative, to avoid overhead associated with the complex structure of the virtualized one
  * 
  * Q: should the return of a block be a trivial expr?!
  * 
  * Implem. Notes
  *   if we make holes not _.isTrivial, we get a SOF in the pretty-printing (which replaces bound vals by holes)
  * 
  * TODO: replace the "early return with transfo" pattern to just recursive transformer calls... (ie: Return.transforming is unnecessary)
  * 
  * TODO optim transformers based on object identity?
  *   make AST's RepTransformer cache what it has applied to and reuse previous results...
  * 
  */
class SimpleANF extends AST with CurryEncoding with SimpleEffects { anf =>
  
  object ANFDebug extends PublicTraceDebug
  
  
  def effectCached(r: Rep) = r.effect
  
  type StmtRep = Either[Val -> Rep, Rep]
  type BlockRep = List[StmtRep] -> Rep // Note: perhaps a repr easier to handle would be: List[Option[Val] -> Rep] -> Rep
  
  override protected def mkCode[T,C](r: Rep): Code[T,C] = r.asInstanceOf[Code[T,C]]
  
  type Occurrence = Range
  object Occurrence {
    val Never = 0 to 0
    val Once = 1 to 1
    val Unknown = 0 to Int.MaxValue
  }
  
  case class Rep(dfn: Def) extends Code[Any,Nothing] {
    val rep = this
    
    def withUnderlyingTyp = this.asInstanceOf[Code[Typ,Nothing]]
    
    def isTrivial = !effect.immediate
    
    lazy val hasImmediateHoles = anf.hasImmediateHoles(this)
    
    lazy val effect = anf.effect(this)
    
    def isPure = isTrivial && !hasImmediateHoles
    
    lazy val isHole: Bool = dfn match {
      case Hole(_) | SplicedHole(_) => true
      case Ascribe(x, _) => x.isHole
      case _ => false
    }
    final def isImpure = !isPure
    
    lazy val asBlock: BlockRep = dfn match {
      case LetIn(p,v,b) => b.asBlock |>= { case es -> r => (Left(p -> v) :: es) -> r }
      case Imperative(effs,ret) => ret.asBlock |>= { case es -> r => ((effs map (e => Right(e)) toList) ++ es) -> r }
      //case MethodApp(s,m,ts,ass,t) => 
      case _ => Nil -> this
    }
    
    lazy val boundVals: Set[Val] = anf.boundVals(this)
    
    def unapply(that: Rep) = extract(this, that)
    
    //override def toString = s"$dfn"  // Now that Rep extends IR (for performance), it's a bad idea to override toString
    override def toString = if (isShowing) s"<currently-showing>$dfn" else super.toString
    
    type OccMap = Map[Rep,Occurrence]
    
    /** Number of times each interesting-to-factor subexpression appears in this tree, including the top-level expression. */
    lazy val occurrences: OccMap = {
      import Occurrence._
      def merge(xs:OccMap, ys:OccMap) = xs ++ (ys map { kv => (xs get kv._1) match {
          case Some(v) => kv._1 -> (kv._2.start + v.start to kv._2.end + v.end)
          case _ => kv
      }})
      dfn match {
        case LetIn(p,v,b) => merge(v.occurrences, b.occurrences filterKeys (!_.dfn.unboundVals(p)))
        case Abs(p,b) => (b.occurrences filterKeys (!_.dfn.unboundVals(p)) mapValues (_ => Unknown)) + (this -> Once)
        // ^ note we add `(this -> Once)` with `+` and not `merge` because we know the node should not contain itself!
        case Module(pre,_,_) => pre.occurrences
        case (_:MethodApp)|(_:Ascribe) => merge(
          if (!effect.immediate) Map(this -> Once) else Map.empty,
          dfn.children.foldLeft(Map.empty:OccMap){ (a,b) => merge(a,b.occurrences) }
        )
        // only factor constants of String type:
        case Constant(_:String) => Map(this -> Once)
        case (_:Constant) | (_:Hole) | (_:SplicedHole) | (_:NewObject) | (_:BoundVal) | (_:StaticModule) => Map.empty
      }
    }
    
  }
  
  
  /** In ANF, we keep only one effect per Imperative call to make their inductive traversal more natural.
    * Important for matching sequences of effects. */
  def mkImperative(effects: Seq[Rep], res: Rep): Rep = {
    effects.foldRight(res)((eff,acc) => Imperative(eff::Nil,acc) |> Rep) // Q: `rep` here causes stack overflows
  }
  /*
  
  TODO(?) remove pure effects from Imperative
  
  */
  /** Normalizes a Def and wraps it in a Rep */
  def rep(dfn: Def) = {
    
    val isImperativeCall = dfn |>? { case Imperative(_, _) => true } Else false
    
    val statements = mutable.Buffer[Either[Val -> Rep, mutable.Buffer[Rep]]]()
    
    def makeStmtIfNecessary(letBound: Bool)(r: Rep): Rep = /*println(s"mkStmt $r") before*/ r match {
      case _ if r.isTrivial && !(r.hasImmediateHoles && isImperativeCall) => r  // Note: not sure between `r.hasHoles` and `r.isHole` here (used to be `r.isHole`)
      // ^ Reason for the `!r.hasHoles` test is that we don't want to have holes disappear from patterns (provokes extractor crashes)
      // A better solution would be to have aggregated usage info in `r` and inline a term containing holes only when the term is used at least once in the body.
      case LetIn(p, v, b) =>
        //assert(!b.boundVals(p),s"$p bound in $b") // should not fail; disabled for perf
        statements += Left(p -> v)
        b |> makeStmtIfNecessary(false)
      case Imperative(effs, ret) =>
        val buf = statements.lastOption match {
          case Some(Right(b)) => b
          case _ => mutable.Buffer[Rep]() alsoApply (b => statements += Right(b))
        }
        buf ++= effs
        ret |> makeStmtIfNecessary(false)
      case _ if letBound => r
      //case _ if letBound || isImperativeCall => r
      case _ if isImperativeCall =>
        //println(r,statements)
        val buf = statements.lastOption match {
          case Some(Right(b)) => b
          case _ => mutable.Buffer[Rep]() alsoApply (b => statements += Right(b))
        }
        if (r isImpure) buf += r
        r
      case _ =>
        //println(s"Binding $r")
        readVal(freshBoundVal(r.typ) alsoApply { v => statements += Left(v -> r) })
    }
    
    def construct(init: Rep) = statements.foldRight(init) {
      case (Left(v -> r), body0) => 
        //println(s"Binding $v in $body0")
        val vr = v|>rep
        val body = if (body0.boundVals(v)) inline(v, body0, vr) else body0
        // ^ inlining v to itself in the body will renew inner bindings of that param, avoiding future conflicts
        MethodApp(lambda(v::Nil, body), Function1ApplySymbol, Nil, Args(r)::Nil, body.typ) |> rep
      case (Right(b), body) => if (b isEmpty) body 
        //else Imperative(b, body) |> Rep  // don't construct multi-effect Imperative's
        else mkImperative(b, body)
    }
    
    val normal = dfn match {
      //case Apply(f,a) => Apply(f,a,dfn.typ) |> Rep
      case LetIn(p, v, b) if v.isPure && !b.hasImmediateHoles =>
        //println(s"Inl $p as $v in $b")
        inline(p, b, v)
        
      // Tail binding normalization:
      case LetIn(p, v, b) if b.dfn === p => v
      case LetIn(p, v, RepDef(Ascribe(b,tp))) if b.dfn === p => ascribe(v,tp)
        
      // Unit value normalization:
      case LetIn(p, v, b) if p.typ <:< UnitType && !(p.typ <:< NothingType) && !(p.isExtractedBinder) => Imperative(v)(inline(p, b, () |> const))
      case Imperative(Seq(e),r) if r.isPure && (e.typ <:< UnitType) && (e.typ <:< r.typ) => e
        
      case Imperative(effs, ret) =>
        //effs foreach { e => e |> makeStmtIfNecessary(false) and (r => statements += Right(r)) }
        effs foreach makeStmtIfNecessary(false)
        //construct(ret |> makeStmtIfNecessary(false))
        val newRet = ret |>=? {
          case Imperative(effs2, ret2) => 
            effs2 foreach makeStmtIfNecessary(false)
            ret2
        }
        construct(newRet)
        
      case MethodApp(s,m,ts,ass,t) =>
        //dfn |>? { case LetIn(p, v, b) => println(p,v,b) }
        val isLetBinding = dfn |>? { case LetIn(_, _, _) => true } Else false
        val newSelf = makeStmtIfNecessary(false)(s)
        val newArgss = ass.map(_.map(anf)(makeStmtIfNecessary(isLetBinding)))
          // ^ If we're handling a let binding, there is no need to let-bind the argument (bound value)
          // We still need to call `makeStmtIfNecessary` just in case what's bound is an imperative block or another let binding!
        val init = {
          //MethodApp(newSelf,m,ts,newArgss,t) |> (if (statements nonEmpty) rep else Rep) |> makeStmtIfNecessary(true) // SOF
          (MethodApp(newSelf,m,ts,newArgss,t) |> (if (statements nonEmpty) rep else Rep)) |>=? {
            case Imperative(es,r) =>
              val buf = statements.lastOption match { // TODO factor
                case Some(Right(b)) => b
                case _ => mutable.Buffer[Rep]() alsoApply (b => statements += Right(b))
              }
              buf ++= es
              r
            case LetIn(p, v, b) if v.isPure =>
              inline(p, b, v)
          }
        } 
        construct(init)
      case _ =>
        //assert(dfn isTrivial)
        Rep(dfn)
    }
    
    // Note: no need to renormalize _after_ postProcess, since what postProcess returns should be normal.
    postProcess(normal)
  }
  override def simpleRep(dfn: Def): Rep = Rep(dfn)
  
  def dfn(r: Rep): Def = r.dfn
  
  def repType(r: Rep): TypeRep = r.dfn.typ
  
  override protected def freshNameImpl(n: Int) = "$"+n
  //override protected def freshNameImpl(n: Int) = "$"
  
  
  /** ANF does tricky stuff with bindings internally, so we need to make sure inlining a value that contains references 
    * to a binding won't see these references captured by existing bindings in the body. */
  override def inline(param: BoundVal, body: Rep, arg: Rep) = {
    val refs = arg |> allValRefs  // `freeVals` not sufficient here as shadowing is not okay (it is mostly okay, but messes with term equivalence)
    require(!arg.boundVals(param))
    //require(!body.boundVals(param))  // too strong; can be useful to do that (cf. `inline(v, body0, v|>rep)` above)
    transformRep(body)(if (body.boundVals & refs isEmpty) identity else {
      // while going down the tree, renew conflicting bound vals:
      case RepDef(a @ Abs(p0,b)) if refs(p0) =>
        val p = p0.renew
        Abs(p, a.inline(p |> rep))(a.typ) |> rep
      case r => r
    }, {
      // while going up the tree, inline the `arg` value:
      case RepDef(`param`) => arg
      case r => r
    })
  }
  
  
  protected def boundVals(r: Rep): Set[Val] = {
    val res = mutable.Set[Val]()
    r |> traversePartial {
      case RepDef(Abs(p,b)) => res += p; true
    }
    res.toSet
  }
  
  /** From the ANF Block repr to corresponding AST node 
    * Note: could optimize: build a Rep with the ANF built in to avoid having it recomputed later */
  protected def constructBlock(b: BlockRep) = {
    val (es, r) = b
    es.foldRight(r) {
      case Left(p -> v) -> b => letin(p, v, b, r.typ)
      case Right(r) -> Imperative(es, ret) => Imperative(r :: es.toList, ret) |> rep
      case Right(r) -> b => Imperative(r::Nil, b) |> rep
    }
  }
  
  
  // When extracting the body of a lambda or let binding, the bound Val is replaced with a Hole that remembers this original Val (in field `originalSymbol`)
  // Here we aggregate all Val references originally present instead of the extraction holes
  protected def originalVals(r: Rep) = {
    val res = mutable.Set[Val]()
    r |> traversePartial {
      case RepDef(h: Hole) => h.originalSymbol foreach (res += _); false
      //case h: SplicedHole => h.originalSymbol
    }
    res
  }
  protected def allValRefs(r: Rep) = {
    val res = mutable.Set[Val]()
    r |> traversePartial {
      case RepDef(bv: BoundVal) => res += bv; false
    }
    res
  }
  // ^ TODO cache these, like for `boundVals`
  
  
  /* TODO flexible spliced holes
   * TODO consecutive mutable statement matching like in PardisIR */
  /** Rewrites a Rep by applying a rewriting on the corresponding ANF block;
    * aborting the rewriting if it removes Vals still used later on. */
  override def rewriteRep(xtor: Rep, xtee: Rep, code: Extract => Option[Rep]): Option[Rep] = /*ANFDebug muteFor*/ {
    import Console.{BOLD, RESET}
    debug(s"${BOLD}Rewriting$RESET $xtee ${BOLD}with$RESET $xtor")
    //nestDbg(extract(xtor, xtee)) and (res => debug(s"${BOLD}Result:$RESET $res"))
    
    /* Backtracking rewriting block matcher
     * @param ex: current extraction artifact
     * @param matchedVals: which bound Vals have been traversed and replaced by holes so far
     * @param xy: the current (extractor -> extractee) pair */
    def rec(ex: Extract, matchedVals: List[Val])(xy: BlockRep -> BlockRep): Option[Rep] = {
      //debug(s"REC ex=$ex")
      
      def checkRefs(r: Rep): Option[Rep] = { // Q: is it sufficient to use `freeVals` instead of `allValRefs` here?
        //debug("Checking refs in "+r)
        val matchedValsSet = matchedVals.toSet
        r optionIf ((originalVals(r) | allValRefs(r)) & matchedValsSet isEmpty) alsoApply_? {
          case None => debug(s"${Console.RED}Rewritten term:${Console.RESET} $r ${Console.RED}contains references to original vals ${originalVals(r)} or free vals ${allValRefs(r)} ${Console.RESET}")
        }
      }
      
      def mkCode(ex: Extract, pre: (Rep, Rep => Rep) => Rep = (r,t)=>r): Option[Rep] = {
        debug(s"${Console.BOLD}Constructing code with $ex${Console.RESET}")
        val r = try code(ex) catch { case e: Throwable =>
          debug(s"${Console.RED}Construction did not complete. ($e)${Console.RESET}")
          e match {
            case EarlyReturnAndContinueExc(cont) =>
              throw EarlyReturnAndContinueExc((trans) => {
                trans |> cont |> (pre(_,trans)) |> checkRefs Else {
                  // Continues to apply the current transformation on the next tree nested in xtee, if any. Note: assumes TopDown order!...
                  xtee.asBlock match {
                    case (st::sts) -> r => constructBlock((st::Nil) -> trans(sts -> r |> constructBlock))
                    case Nil -> r => r
                  }
                }
              })
            case _ => throw e
          }
        }
        debug(s"${Console.GREEN}Constructed: ${r map showRep}${Console.RESET}")
        r flatMap checkRefs
      }
      
      xy match {
          
        // Matching simple expressions (block returns)
        case (Nil -> r0, Nil -> r1) =>
          for {
            e <- extract(r0, r1)
            m <- merge(e, ex)
            c <- mkCode(m)
          } yield c
          
        //// TODO allow extraction of several statements with a hole in effect position? Or a bound hole? (to preserve context soundness) 
        //case (sts0 -> r0, (Right(e1) :: es1) -> r1) if e1.isHole =>
          
        // Matching two effects
        case ((Right(e0) :: es0) -> r0, (Right(e1) :: es1) -> r1) =>
          extract(e0, e1) flatMap (merge(_, ex)) flatMap (rec(_, matchedVals)(es0 -> r0, es1 -> r1))
          
        // Matching an two let bindings (eg: {val a = readInt; ...} with {val x = readInt; $body: Int})
        case ((Left(b0 -> v0) :: es0) -> r0, (Left(b1 -> v1) :: es1) -> r1) =>
          for {
            e <- extract(v0, v1)
            (hExtr,h) = b1.toHole(b0)
            e <- merge(e, ex)
            e <- merge(e, hExtr)
            hr = rep(h)
            //() = debug(s"Extracting binder $b1: $hr")
            es1i = es1 map {
              case Right(r) => Right(inline(b1, r, hr))
              case Left(b -> v) => Left(b -> inline(b1, v, hr))
            }
            r1i = inline(b1, r1, hr)
            r <- rec(e, b1 :: matchedVals)(es0 -> r0, es1i -> r1i)
          } yield r
          
        // Matching an effect with a let binding (eg: {readInt; 42} with {val r = readInt; $body: Int})
        case ((Right(v0) :: es0) -> r0, (Left(b1 -> v1) :: es1) -> r1) =>
          for {
            e <- extract(v0, v1)
            e <- merge(e, ex)
            r <- rec(e, b1 :: matchedVals)(es0 -> r0, es1 -> r1)
          } yield r
          
        case ((Left(b0 -> v0) :: es0) -> r0, (Right(v1) :: es1) -> r1) => // Later, use more compact block repr and merge w/ above
          for {
            e <- extract(v0, v1)
            e <- merge(e, ex)
            r <- rec(e, matchedVals)(es0 -> r0, es1 -> r1)
          } yield r
          
        // Matching a whole block with a hole
        case (Nil -> r, bl) if r.isHole =>
          // TODO specially handle SplicedHole?
          // TODO also try eating less code? (backtracking)
          extract(r, bl |> constructBlock) flatMap (merge(_, ex)) flatMap (mkCode(_))
          
        // Matching an arbitrary statement of a block with the last expression of an xtor
        // -- rewriting can happen in the middle of a Block, and then we have to ensure later terms do not reference removed bindings
        case (Nil -> r0, (stmt :: es) -> r1) =>
          val (rep, rebuild) = stmt match {
            case Left(b -> v) => v -> ((x:Rep) => Left(b -> x))
            case Right(r) => r -> ((x:Rep) => Right(x))
          }
          for {
            e <- extract(r0, rep)
            e <- merge(e, ex)
            c <- mkCode(e, (lhs,trans) => {
              //debug("LHS "+lhs)
              val newRest = constructBlock(es->r1)
              //debug("NR "+newRest)
              constructBlock((rebuild(lhs)::Nil) -> trans(newRest))
            })
            r <- constructBlock((rebuild(c) :: es) -> r1) |> checkRefs
          } yield r
          
        case _ => None
    
      }
    }
    
    if (xtor.asBlock._1.isEmpty && xtee.asBlock._1.nonEmpty) return None
    // ^ TODO handle `{val r = expr; r}` as well as `expr`
    
    rec(repExtract(SCRUTINEE_KEY -> xtee),Nil)(xtor.asBlock -> xtee.asBlock) alsoApply_?
      { case Some(r) => debug(s"${BOLD}=> Rewrote$RESET $r") }
    
  }
  
  
  
  
  
  
  
  
  
  
  
  // Currently, the purpose of the following is only to build nice flat Scala trees from nested imperatives...
  // may be simpler to just add a switch to the super.ReinterpreterToScala impl 
  
  import squid.quasi.MetaBases
  import utils.meta.{RuntimeUniverseHelpers => ruh}
  import ruh.sru
  
  override def scalaTreeIn(MBM: MetaBases)(SRB: MBM.ScalaReflectionBase, rep: Rep, ExtrudedHandle: (BoundVal => MBM.u.Tree)): MBM.u.Tree = ANFDebug.muteFor { muteFor {
    new ReinterpreterToScala {
      val MetaBases: MBM.type = MBM
      val newBase: SRB.type = SRB
      override val extrudedHandle = ExtrudedHandle
    } apply rep
  }}
  
  abstract class ReinterpreterToScala extends super.ReinterpreterToScala {
    val MetaBases: MetaBases
    import MetaBases.u._
    val newBase: MetaBases.ScalaReflectionBase
    
    //val repCache = mutable.Map[Int, newBase.Rep]()
    
    override def apply(d: Def) = d match {
      case Imperative(es,r) => q"..${es map apply}; ..${r |> apply}"
      case _ => super.apply(d)
    }
  }
  
}




















