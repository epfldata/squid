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

import squid.lang.Base
import squid.lang.InspectableBase
import squid.lang.{RecRewrite,TopDownRewrite}
import squid.quasi.EmbeddingException
import squid.quasi.QuasiBase
import squid.utils.MacroUtils.{MacroSetting, MacroDebug, MacroDebugger}
import utils._
import utils.CollectionUtils._

import scala.language.experimental.macros
import utils.UnknownContext

import scala.collection.mutable

case class RewriteAbort(msg: String = "") extends Exception

/** Type and context-safe interface for rewrite-rule-based program transformation.
  * It checks that rewrite rules rewrite things to the same type, and with a weaker or identical context.
  * Turns {{{ rewrite { case ir"<pat a,b..>" => <code a,b..> ... }}} expressions into expressions of the form:
  * {{{ registerRule(ir"<pat a,b..>", (x: Extract) => val a,b.. = x; <code a,b..>) }}}
  * 
  * TODO: better handling of situations where cases do not have the right shape
  * 
  * TODO: use standard errors rather than bare aborts
  * 
  **/
trait RuleBasedTransformer extends Transformer {
  import base._
  
  def rewrite(tr: Code[Any,UnknownContext] => Code[Any,_]): Unit = macro RuleBasedTransformerMacros.rewrite
  @MacroSetting(debug = true) def dbg_rewrite(tr: Code[Any,UnknownContext] => Code[Any,_]): Unit = macro RuleBasedTransformerMacros.rewrite
  
  /** Register a transformation where the pattern is enceded with an extractor ("xtor") Rep and an associated function
    * `code` that makes use of what is extracted. `code` may return None in case a condition for its application is not
    * met (eg: the case in a rewriting had a condition guard) */
  def registerRule(xtor: Rep, code: Extract => Option[Rep]): Unit
  
}

import reflect.macros.whitebox
class RuleBasedTransformerMacros(val c: whitebox.Context) {
  import c.universe._
  
  val debug = { val mc = MacroDebugger(c); mc[MacroDebug] }
  
  object Helpers extends {val uni: c.universe.type = c.universe} with quasi.ScopeAnalyser[c.universe.type]
  import Helpers._
  
  val VariableSymbol = Lazy(c.symbolOf[QuasiBase#Variable[Any]])
  
  
  /** Hack to work around local variables defined on the right-hand side of a rewrite rule, which path-dependent types
    * get messed up when the local variable's symbol is recomputed from scratch, which is a problem when these PDTs are
    * involved in the context of quoted code.
    * `variableSymbols` saves the association from fresh names to old symbols, and `putBackVariableSymbols`
    * re-associates val-bindings with these symbols (presumably after they have been lost due to c.untypecheck).
    * Currently we only do this for val-bindings of the shape `val v = new Variable[T]` */
  def putBackVariableSymbols(pgrm: Tree) = TreeOps(pgrm).transform {
    case v @ ValDef(mods, name, tpt, rhs) if variableSymbols isDefinedAt name =>
        val sym = variableSymbols(name)
        q"$mods val ${sym.name} = $rhs.asInstanceOf[$sym.type]"
  }
  val variableSymbols = mutable.Map.empty[c.TermName,c.universe.TermSymbol]
  
  
  def termRewrite(tr: c.Tree) = {
    
    val (baseTree,termTree,typ,ctx) = c.macroApplication match {
      case q"$base.InspectableCodeOps[$t,$c]($term).$_($_)" =>
        (base, term, t.tpe, c.tpe)
      case q"$base.InspectableAnyCodeOps[$t]($term).$_($_)" =>
        (base, term, t.tpe, Nothing)
    }
    val base = baseTree
    debug(s"Found base `${showCode(base)}` of type `${base.tpe}`")
    
    val transName = TermName(c.freshName("trans"))
    
    val (rwTree,ctxTrans) = rewriteImpl(tr, q"$transName", base)
    
    //debug("ctxTrans:",ctxTrans)
    
    val outputContext = {
      val (initBases, initVars) = bases_variables(ctx)
      val (newBases, newVars) = ctxTrans map {
        case (extractedCtx, constructedCtx, constructedPos) =>
          debug(s"XC $extractedCtx  CC $constructedCtx")
          val (bases,variables) = bases_variables(constructedCtx)
          debug(s"bases: $bases -- ${bases filterNot (_ <:< extractedCtx)}")
          (bases filterNot (_ <:< extractedCtx), variables)
      } unzip;
      mkContext(initBases :: newBases flatten, initVars :: newVars flatten)
    }
    
    debug("outputContext:",outputContext)
    
    val recursive = c.macroApplication.symbol.annotations.exists(_.tree.tpe <:< typeOf[RecRewrite])
    val topDown = c.macroApplication.symbol.annotations.exists(_.tree.tpe <:< typeOf[TopDownRewrite])
    val RuleBasedTrans = 
      (if (recursive) tq"_root_.squid.ir.FixPointRuleBasedTransformer" else tq"_root_.squid.ir.SimpleRuleBasedTransformer") ::
      (if (topDown) tq"_root_.squid.ir.TopDownTransformer" else tq"_root_.squid.ir.BottomUpTransformer") ::
      Nil
    
    //val $transName = new _root_.scp.ir.SimpleRuleBasedTransformer with _root_.scp.ir.TopDownTransformer {
    //val $transName: _root_.scp.ir.Transformer{val base: ${base.tpe} } = new _root_.scp.ir.SimpleTransformer {
    //object $transName extends _root_.scp.ir.SimpleRuleBasedTransformer with _root_.scp.ir.TopDownTransformer {  // Note: when erroneous, raises weird "no progress" compiler error that a `val _ = new _` would not
    // TODO give possibility to chose transformer (w/ implicit?)
    var res = q"""
    object $transName extends ..$RuleBasedTrans {  // Note: when erroneous, raises weird "no progress" compiler error that a `val _ = new _` would not
      val base: ${base.tpe} = $base
    }
    ${rwTree}
    $base.`internal Code`[$typ,$outputContext]($transName.optimizeRep($termTree.rep.asInstanceOf[$transName.base.Rep]).asInstanceOf[$base.Rep])
    """
    
    res = putBackVariableSymbols(res)
    
    debug("Generated: " + showCode(res))
    
    //debug("Generated: " + (res))
    //debug("Generated: " + showCode(c.untypecheck(res)))
    //debug("Generated: " + showRaw(c.untypecheck(res)))
    
    //res // crashes
    c.untypecheck(res)
    //c.parse(showCode(res))
    
  }
  
  
  def rewrite(tr: c.Tree) = {
    
    val trans = c.macroApplication match {
      case q"$trans.rewrite($_)" => trans
      case q"$trans.dbg_rewrite($_)" => trans
      case q"$trans.rec_rewrite($_)" => trans
    }
    var base = c.typecheck(q"$trans.base")
    base = internal.setType(base, c.typecheck(tq"$trans.base.type", c.TYPEmode).tpe)
    // ^ For some reason, when `trans` is of the form `SomeClass.this`, we get for `base.tpe` a widened type... so here we explicitly ask for the singleton type
    debug(s"Found base `${showCode(base)}` of type `${base.tpe}`")
    
    //val res = rewriteImpl(tr, trans, base)
    val (res,ctxTrans) = rewriteImpl(tr, trans, base)
    
    ctxTrans foreach {
      case (extractedCtx, constructedCtx, constructedPos) =>
        if (!(extractedCtx <:< constructedCtx))
          c.abort(constructedPos,
            if (constructedCtx <:< extractedCtx)
              s"Cannot rewrite a term of context $extractedCtx to a stricter context $constructedCtx"
            else s"Cannot rewrite a term of context $extractedCtx to an unrelated context $constructedCtx")
    }
    
    val finalRes = c.untypecheck(putBackVariableSymbols(res))
    /* it looks like doing this before or after untypecheck does not have any incidence on the result */
    //val finalRes = putBackVariableSymbols(c.untypecheck(res))
    
    debug("Generated: " + showCode(finalRes))
    
    finalRes
  }
  
  /** Returns the result rewrite-registering tree plus a list of tuples of the extracted context,
    * the constructed context, and the constructed context tree position */
  def rewriteImpl(tr: c.Tree, trans: c.Tree, base: c.Tree): (c.Tree, List[(c.Type,c.Type,c.Position)]) = {
    
    val cases = tr match {
      case Function(ValDef(_, name, _, _) :: Nil, q"$_ match { case ..$cases }") => cases
    }
    
    //debug(cases)
    
    var n = 0
    
    val (registrations, ctxTrans) = cases map {
      case cas @ CaseDef(pat, cond, expr) =>
        
        n += 1
        debug(s" --- CASE #$n --- ")
        
        def notFound(obj: String) = c.abort(cas.pos, s"Could not determine $obj for that case: ${showCode(pat)}")
        
        // Note: there is not much we can do in case the pattern is NOT a quasiquote (eg: a single `case e =>`, since 
        // that pattern will have been typed with UnknownContext, and it's too late to change that at this point – or
        // perhaps not, but it would introduce even more complexity to this macro.
        // // pat |>? { case t @ Bind(name, Ident(TermName("_"))) => ... } getOrElse (...
        val extractedType = (pat.find {
          case td@TypeDef(_, TypeName("$ExtractedType$"), _, _) => true
          case _ => false
        } getOrElse notFound("extracted type")).symbol.asType.typeSignature
        val extractedCtx = (pat.find {
          case td@TypeDef(_, TypeName("$ExtractedContext$"), _, _) => true
          case _ => false
        } getOrElse notFound("extracted context")).symbol.asType.typeSignature
        
        def badType(constructedType: Type, constructedPos: Position) =
          c.abort(constructedPos, s"Cannot rewrite a term of type $extractedType to a different type $constructedType")
        
        val constructedPos = expr match {
          case Block(_, r) => r.pos
          case _ => expr.pos
        }
        var constructedCtx = expr.tpe.baseType(symbolOf[Base#Code[_, _]]) match {
          case tpe@TypeRef(tpbase, _, constructedType :: constructedCtx :: Nil) =>
            assert(tpbase =:= base.tpe, s"Base types `$tpbase` and `${base.tpe}` (type of ${showCode(base)}) are different.")
            
            if (constructedType <:< extractedType) {
              //debug("Rewriting " + extractedType)
            } else {
              badType(constructedType, constructedPos)
            }
            constructedCtx
            
          case NoType if Nothing <:< expr.tpe => // For example if the user ends a rewrite with a 'throw' or '???' for debugginh purposes
            // FIXME later we get: Error:(182, 13) value rep is not a member of Nothing
            Any
            
          case NoType =>
            c.abort(constructedPos, s"This rewriting does not produce a ${base.tpe}.Code[_,_] type as a return.")
            
        }
        
        debug("Base CC:",constructedCtx)
        
        def processEarlyReturn(b:Tree,tp:Tree,cx:Tree,pos:Position) = {
          if (b.tpe =:= base.tpe) {
            debug("Return introduces context "+cx.tpe)
            constructedCtx = glb(constructedCtx :: cx.tpe :: Nil)
            val constructedType = tp.tpe
            if (constructedType <:< extractedType) true
            else badType(constructedType, pos)
          } else { // TODO test this
            val bs = showCode(b)
            c.warning(b.pos, s"`$bs.Return` is invoked where `$bs` may not be the same as ${showCode(base)}")
            false
          }
        }
        
        // Transforms calls to transformation-control operators Predef.Abort, Predef.Return and Predef.Return.transforming
        // into their underlying impl and aggregates associated type and context info
        // TODO also do it for pattern guard!
        val newExpr = expr transform {
          case t @ q"$b.Predef.Abort($msg)" if b.tpe <:< typeOf[QuasiBase] =>
            q"$b.`internal abort`($msg)"
          case t @ q"${r @ q"$b.Predef.Return"}.apply[$tp,$cx]($v)" if b.tpe <:< typeOf[InspectableBase] =>
            if (processEarlyReturn(b,tp,cx,r.pos)) q"$b.`internal return`[$tp,$cx]($v)" else t
          case t @ q"${r @ q"$b.Predef.Return"}.transforming[..$ts](...$as)" if b.tpe <:< typeOf[InspectableBase] =>
            val List(cx,tp,_ @ _*) = ts.reverse
            if (processEarlyReturn(b,tp,cx,r.pos)) q"$b.`internal return transforming`[..$ts](...$as)" else t
          case t @ q"${r @ q"$b.Predef.Return"}.recursing[$tp,$cx]($cont)" if b.tpe <:< typeOf[InspectableBase] =>
            if (processEarlyReturn(b,tp,cx,r.pos)) q"$b.`internal return recursing`[$tp,$cx]($cont)" else t
            
          // cf. documentation of `putBackVariableSymbols`
          // I tried doing this for general value bindings (with conditions such as
          //   `if rhs.nonEmpty && v.symbol.isTerm && v.symbol.asTerm.isStable && v.symbol.typeSignature <:< AnyRef`),
          // but it usually does not work... even if we manually type-check the tree and abort on type checking errors
          case v @ ValDef(mods, name, tpt, rhs @ q"new $base.Variable[$typ]($nam)($typev)") => // TODO check base
            val fn = c.freshName(name)
            variableSymbols += (fn -> v.symbol.asTerm)
            ValDef(mods, fn, tpt, rhs)
            // ^ Note: not recursing into the subtrees... move this to `val gen0 = TreeOps(res).transformRec` if need arises
            
        }
        
        debug("XC",extractedCtx,"CC",constructedCtx)
        
        //val baseBinding = pat.find {
        //  case q"val __b__ : $_ = $_" => true
        //  case _ => false
        //} get;
        
        val termTree = pat.find {
          case q"val _term_ : $_ = __b__.wrapExtract($termTree)" => true
          case _ => false
        } match { case Some(ValDef(_, _, _, rhs)) => rhs } // Note: we keep the `wrapExtract`
        //} match { case Some(ValDef(_, _, _, rhs)) => rhs  case _ => return q"???" -> Nil } // Note: we keep the `wrapExtract`
        //} match { case Some(ValDef(_, _, _, q"__b__.wrapExtract($termTree)")) => termTree }
        
        
        val (alias, xtor, subPatterns) = pat match {
          case UnApply(fun, args) => (None, fun, args)
          case Bind(alias, UnApply(fun, args)) => (Some(alias), fun, args)
          case _ => throw EmbeddingException("Unrecognized pattern shape: "+showCode(pat))
        }
        
        /** List[(name of the map in the Extract artifact, pattern name)] */
        val patNames = xtor.collect {
          case q"_maps_.${tn @ TermName(tnStr)}.apply(${Literal(Constant(name: String))})" =>
            assert(tnStr.startsWith("_"))
            tn -> name
        }
        
        assert(subPatterns.size == patNames.size, s"$subPatterns did not coincide in size with $patNames")
        
        /** Rewrites UnApply trees introduced by typechecking to normal trees recursively, so we can typecheck again later. */
        // Q: with nested rewrite rules, doesn't this virtualizes pattern matching several times, 
        // resulting in very bad code? (indeed, we do produce normal patmat as a result here)
        def patMat(scrut: Tree, pat: Tree, body: Tree): Tree = {
          pat match {
            case UnApply(fun, args) =>
              val unapp = TreeOps(fun) transform { case Ident(TermName("<unapply-selector>")) => scrut }
              if (fun.tpe <:< typeOf[Boolean]) {
                q"if ($unapp) $body else None"
              }
              else {
                val args_names = args.zipWithIndex map (ai => ai._1 -> TermName("__"+ai._2))
                q"$unapp flatMap { case (..${args_names map { case (arg, nam) => pq"$nam: ${arg.tpe.widen} @unchecked" }}) => ${
                // using `.widen` so that things like `:String("abc")` become just `:String` ^
                  (args_names :\ body) {
                    case ((arg, nam), acc) => patMat(q"$nam", arg, acc)
                  }
                }}" 
                //} case _ => None }" // such default case is not useful as long as we widen `arg.tpe`; otherwise when
                // matching a constant, as in `case ir"println(${Const("abc")}:String)"`, the type of the pattern variable
                // would be String("abc") and the matching would fail...
                // OTOH, maybe there are other cases where the pattern variable would have a type that is too precise,
                // eg maybe when matching a vararg with a host-language List instead of Seq... but it's not clear that
                // in this case we really want to silently fail the matching...
              }
            //case Bind(name: TermName, pq"_") => q"val $name = $scrut; ..$body"
            case b@Bind(name: TermName, pq"_") => // For some reason, this seems to be necessary for the gen0/gen phase below to work!! 
              q"${internal.valDef(b.symbol,scrut)}; ..$body"
            case b@Bind(name: TermName, pat) =>
              val scrutName = TermName(c.freshName("scrut"))
              q"val $scrutName = $scrut; ${internal.valDef(b.symbol,q"$scrutName")}; ${patMat(q"$scrutName", pat, body)}"
            case k @ Literal(Constant(c)) =>
              q"if ($scrut == $k) $body else None"
            case p => throw EmbeddingException(s"Pattern shape not yet supported in rewrite rule: ${showCode(p)}")
          }
        }
        
        val patAlias = alias match {
          case Some(a) => q"""val ${a.toTermName} = __b__.`internal Code`[Any,_root_.squid.utils.UnknownContext](__extr__._1($SCRUTINEE_KEY))"""
          case None => q""
        }
        
        debug(s"PATTERN ALIAS: ${showCode(patAlias)}")
        
        val exprRep = q"($newExpr:__b__.Code[_,_]).rep"
        
        val r = q"$trans.registerRule($termTree.asInstanceOf[$trans.base.Rep], ((__extr__ : $base.Extract) => ${
        //val r = q"$baseBinding; $trans.registerRule($termTree.asInstanceOf[$trans.base.Rep], (__extr__ : $base.Extract) => ${
          ((subPatterns zip patNames) :\ (
              if (cond.isEmpty) q"..$patAlias; _root_.scala.Option($exprRep).asInstanceOf[Option[$trans.base.Rep]]"
              else q"..$patAlias; if ($cond) _root_.scala.Some($exprRep) else _root_.scala.None") ) {
            
            case ((pat, (mapName @ TermName("_1"), name)), acc) =>
              // Here, there are two possible cases to consider:
              //  - either the retrieved term is used as a normal Code term
              //  - or it is used as a Variable (cf: extracted binders syntax `val $a = ...` or `($a:T) => ...`)
              pat.tpe.baseType(VariableSymbol.value) match { // here we distinguish in which case we are, based on expected pattern type
                case NoType => patMat(q"__b__.`internal Code`(__extr__.$mapName($name))", pat, acc)
                case TypeRef(_,_,_) => patMat(q"__b__.Variable(__b__.extractVal(__extr__.$mapName($name)).get).asInstanceOf[${pat.tpe}]", pat, acc)
              }
              
            case ((pat, (mapName @ TermName("_2"), name)), acc) =>
              patMat(q"__b__.`internal CodeType`(__extr__.$mapName($name))", pat, acc)
              
            case ((pat, (mapName @ TermName("_3"), name)), acc) =>
              patMat(q"(__extr__.$mapName($name)) map ((__rep__ : __b__.Rep) => __b__.`internal Code`(__rep__))", pat, acc)
              
          }
        }).asInstanceOf[$trans.base.Extract => _root_.scala.Option[$trans.base.Rep]])"
        
        //debug(r)
        
        r -> (extractedCtx, constructedCtx, constructedPos)
    } unzip;
    
    
    val res = q"val __b__ : ${base.tpe} = $base; ..$registrations"
    //val res = q"..$registrations"
    
    //debug("Result: "+showCode(res))
    
    // Resets previously resolved identifier symbols; necessary since we're defining a new binding for __b__
    //val gen = TreeOps(res) transform { case Ident(name) => Ident(name) }
    
    // TODO properly fix owner chain corruptions
    
    
    /* What follows is a crazy hack to prevent owner corruption crashes and type symbol mismatches. */
    
    val knownTrees = mutable.Map[Type,Tree]()
    
    val gen0 = TreeOps(res).transformRec(rec => {
        
      // Removes symbol references from identifiers, including those in type trees (see case below)
      // Note: removing these just for terms is enough to avoid Scalac crashes
      case id @ Ident(name) =>
        //debug(s"Refreshing ident $id")
        Ident(name)
        
      // Reverts types to their original tree if available, so they are retyped and lose old symbol references
      case tt @ TypeTree() if tt.original =/= null =>
        
        //debug(s"Getting original of type $tt -> ${tt.original}")
        val res = rec(tt.original)
        if (tt.tpe =/= null) knownTrees += tt.tpe -> res
        
        //if (tt.tpe =/= null) knownTrees += tt.tpe.dealias -> res
        /* ^ Dealiasing can break some transformers, as it can expose a bare extracted type as an identifier (eg change t.Typ to t),
         * which is not in scope (note: maybe could add a new one in scope), but that would probably be even more of a mess. */
        res
        
      //case ts @ Select(path,name) => Select(rec(path),name) // <- Not necessary
    })
     
    val gen = gen0 transform {
    
      // Transforms remaining TypeTree's (that don't have an original tree) if we have tramsformed a TypeTree with the same type before!   
      case tt @ TypeTree() if tt.tpe =/= null =>
        //debug(s"REMAINING $tt ${tt.tpe} ${knownTrees isDefinedAt tt.tpe}")
        knownTrees get tt.tpe getOrElse tt
        
        //knownTrees get tt.tpe.dealias getOrElse tt 
    }
    
    //val gen = res
    
    //debug("Typed: "+c.typecheck(gen))
    //debug("Generated: "+(gen))
    //debug("Generated: "+showCode(gen))
    
    /*debug(" --- GENERATED ---\n"+showCode(gen))*/
    
    gen -> ctxTrans
    
  }
  
}






