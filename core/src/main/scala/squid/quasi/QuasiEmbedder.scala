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
import squid.utils.MacroUtils._

import collection.mutable
import reflect.macros.TypecheckException
import utils.CollectionUtils._
import squid.lang.Base

import scala.reflect.macros.whitebox


case class QuasiException(msg: String, pos: Option[scala.reflect.api.Position] = None) extends Exception(msg)

object QuasiEmbedder {
  private val knownSubtypes = mutable.ArrayBuffer[Any]()
}
import QuasiEmbedder._

/** Holes represent free variables and free types (introduced as unquotes in a pattern or alternative unquotes in expressions).
  * Here, insertion unquotes are _not_ viewed as holes (they should simply correspond to a base.$[T,C](tree) node).
  * 
  * Note: this class produces output that is very closely coupled with the RuleBasedTransformer#rewriteImpl macro;
  * consequently, changes in the shape of generated code here may affect/break the `rewrite` macro.
  * 
  */
class QuasiEmbedder[C <: whitebox.Context](val c: C) {
  import c.universe._
  
  object Helpers extends {val uni: c.universe.type = c.universe} with ScopeAnalyser[c.universe.type]
  import Helpers._
  
  val debug = { val mc = MacroDebugger(c); mc[MacroDebug] }
  
  val rc = c.asInstanceOf[reflect.macros.runtime.Context]
  import rc.universe.analyzer.{Context=>RCtx}
  
  /** Stores known subtyping knowledge extracted during pattern matching, 
    * along with the scope (scala compiler context) in which they are true. */
  val curTypeEqs = knownSubtypes.asInstanceOf[mutable.ArrayBuffer[(RCtx,Type,Type)]]
  
  val UnknownContext = typeOf[utils.UnknownContext]
  val scal = q"_root_.scala"
  
  
  lazy val VariableCtxSym = symbolOf[QuasiBase#Variable[Any]#Ctx]
  def variableContext(tree: Tree) = {
    val singt = singletonTypeOf(tree).getOrElse(throw QuasiException(
      s"Cannot use variable of non-singleton type ${tree.tpe}",
      Some(tree.pos)
    ))
    c.typecheck(tq"$singt#Ctx",c.TYPEmode).tpe
    /* ^ note: things that did not work:
           c.internal.typeRef(singt,VariableCtxSym,Nil);
           singt.member(TermName("Ctx")).asType.toType */
  }
  def singletonTypeOf(tree: Tree): Option[Type] = tree.tpe match {
    case SingleType(_,_) => Some(tree.tpe)
    case _ => tree |>? {
      case Ident(name) => val id = Ident(name); c.typecheck(q"$id:$id.type").tpe
    }
  }
  

  /** holes: Seq(either term or type); splicedHoles: which holes are spliced term holes (eg: List($xs*))
    * holes in ction mode are interpreted as free variables (and are never spliced)
    * unquotedTypes contains the types unquoted in (in ction mode with $ and in xtion mode with $$)
    * TODO: actually use `unquotedTypes`!
    * TODO maybe this should go in QuasiMacros... */
  def applyQQ(Base: Tree, tree: c.Tree, holes: Seq[Either[TermName,TypeName]], 
            splicedHoles: collection.Set[TermName], hopvHoles: collection.Map[TermName,List[List[TermName]]],
            typeBounds: Map[TypeName,EitherOrBoth[Tree,Tree]],
            unquotedTypes: Seq[(TypeName, Type, Tree)], unapply: Option[c.Tree], config: QuasiConfig): c.Tree = {
    
    //debug("HOLES:",holes)
    
    debug("Tree:", tree)
    
    val (termHoles, typeHoles) = holes.mapSplit(identity) match {case (termHoles, typeHoles) => (termHoles toSet, typeHoles toSet)}
    
    /* We used to use local traits to generate local symbols for the type holes; for `case ir"foo[$t]" =>`, term `t` would 
       appear as having type `CodeType[t]`.
       Now, in order to be able to add arbitrary bounds to type holes, we generate a local object with a `Typ` type member,
       so the type above appears as `CodeType[t.Typ]`, which is nice because it's exactly the syntax the user has to use to 
       refer to such an extracted type.
    */
    // val traits = typeHoles map { typ => q"trait $typ extends _root_.squid.quasi.QuasiBase.`<extruded type>`" }  // QuasiBase.HoleType
    val traits = typeHoles flatMap { typ => 
      // Note: cannot use undefined `type` members here, as "only classes can have declared but undefined members"
      val trm = typ.toTermName
      //we used to generate: q"object $trm { type Typ <: _root_.squid.quasi.QuasiBase.`<extruded type>` }"
      val extrudedType = tq"_root_.squid.quasi.QuasiBase.`<extruded type>`"
      val (lb,ub) = typeBounds get typ map {
        case First (lb   ) => lb -> tq"Any" // extrudedType
        // ^ when a lower bound is present, keeping `<extruded type>` in the upper bound will usually make bad bounds, so we do not put it in this case
        case Second(   ub) => tq"Nothing" -> tq"$extrudedType with $ub"
        case Both  (lb,ub) => lb -> ub // tq"$extrudedType with $ub"
      } getOrElse tq"Nothing" -> extrudedType
      q"object $trm { type Typ >: $lb <: $ub }" :: q"type $typ = $trm.Typ @_root_.squid.quasi.Extracted" :: Nil
      }
    
    val vals = termHoles map { vname => q"val $vname: Nothing = ???" }
    
    val curCtxs = rc.callsiteTyper.context.enclosingContextChain
    val (convNames, convs) = curTypeEqs.flatMap {
      case (ctx,lhs,rhs) => 
        if (curCtxs.contains(ctx)) {
          val fresh = TermName(c.freshName("__conv"))
          //q"implicit def $fresh: $lhs <:< $rhs = null" :: Nil
          fresh -> q"implicit def $fresh: _root_.scala.Predef.<:<[$lhs,$rhs] = null" :: Nil
        }
        else Nil
    } .unzip .mapFirst (_.toSet)  // same as:  |> { case (a,b) => (a.toSet,b) }
    debug(s"Subtype knowledge: ${convs.map(t => showCode(t.tpt)).mkString(", ")}")
    
    var termScope: List[Type] = Nil // will contain the scrutinee's scope or nothing
    
    var scrutineeType = Option.empty[Type]
    
    val ascribedTree = unapply match {
      case Some(t) =>
        debug("Scrutinee type:", t.tpe)
        def mkTree(tp: Type) =
          if (tp.typeSymbol.isClass && !(Any <:< tp)) {
            // ^ If the scrutinee is 'Any', we're better off with no ascription at all, as something like:
            // 'List(1,2,3) map (_ + 1): Any' will typecheck to:
            // 'List[Int](1, 2, 3).map[Int, Any]((x$1: Int) => x$1+1)(List.canBuildFrom[Int]): scala.Any'
            tp match {
              case _: ConstantType => None // For some stupid reason, Scala typechecks `(($hole: String): String("Hello"))` as `"Hello"` ..................
              case _ =>
                val purged = purgedTypeToTree(tp)
                debug("Purged matched type:", purged)
                Some(q"$tree: $purged") // doesn't work to force subterms of covariant result to acquire the right type params.....
                //Some(q"_root_.scala.Predef.identity[$purged]($virtualizedTree)") // nope, this neither
            }
          } else None
        t.tpe.baseType(symbolOf[QuasiBase#Code[_,_]]) match {
          case tpe @ TypeRef(tpbase, _, tp::ctx::Nil) =>
            scrutineeType = Some(tp)
            if (!(tpbase =:= Base.tpe)) throw EmbeddingException(s"Could not verify that `$tpbase` is the same as `${Base.tpe}`")
            val newCtx = if (ctx <:< UnknownContext) {
              // ^ UnknownContext is used as the dummy context parameter of terms rewritten in rewrite rules
              // It gets replaced by a brand new type to avoid wrongful sharing, as below:
              
              // Creates a brand new type for this particular context, so that it cannot be expressed outside of the rewrite rule (and thus one can't mix up rewriting contexts)
              val tname = TypeName(s"<context @ ${t.pos.line}:${t.pos.column}>")
              c.typecheck(q"class $tname; new $tname").tpe
              
            } else ctx
            debug("New context:",newCtx)
            termScope ::= newCtx
            mkTree(tp)
          case NoType =>
            t.tpe.baseType(symbolOf[QuasiBase#AnyCode[_]]) match {
              case tpe @ TypeRef(tpbase, _, tp::Nil) => // Note: cf. [INV:Quasi:reptyp] we know this type is of the form Code[_], as is ensured in Quasi.unapplyImpl
                scrutineeType = Some(tp)
                if (!(tpbase =:= Base.tpe)) throw EmbeddingException(s"Could not verify that `$tpbase` is the same as `${Base.tpe}`")
                termScope ::= Any
                mkTree(tp)
              case NoType => assert(false, "Unexpected type: "+t.tpe); ??? // cf. [INV:Quasi:reptyp]
            }
        }
      case None => None
    }
    
    def shallowTree(t: Tree) = {
      // we need tp introduce a dummy val in case there are no statements; otherwise we may remove the wrong statements when extracting the typed term
      val nonEmptyVals = if (traits.size + vals.size + convs.size == 0) Set(q"val $$dummy$$ = ???") else vals ++ convs
      val st = q"..$traits; ..$nonEmptyVals; $t"
      //val st = q"object Traits { ..$traits; }; import Traits._; ..$nonEmptyVals; $t"
      // ^ this has the advantage that when types are taken out of scope, their name is preserved (good for error message),
      // but it caused other problems... the implicit evidences generated for them did not seem to work
      if (debug.debugOptionEnabled) debug("Shallow Tree: "+showCode(st))
      st
    }
    
    /** Note: 'typedTreeType' is actually the type of the tree ASCRIBED with the scrutinee's type if possible... */
    val (typedTree, typedTreeType) = ascribedTree flatMap { t =>
      val st = shallowTree(t)
      try {
        val typed = c.typecheck(st)
        //val q"..$stmts; $finalTree: $_" = typed // Was having some match errors; maybe the ascription was removed when the type was not widened
        val (stmts, finalTree) = typed match {
          case q"..$stmts; $finalTree: $_" => stmts -> finalTree  // ie:  case Block(stmts, q"$finalTree: $_") =>
          //case q"..$stmts; $finalTree" => stmts -> finalTree // Note: apparently, typechecking can remove type ascriptions... (does not seem to happen anymore, though)
        }
        // Since the precise type is needed to define $ExtractedType$:
        Some( internal.setType(q"..$stmts; $finalTree", finalTree.tpe), typed.tpe )
      } catch {
        case e: TypecheckException =>
          debug("Ascribed tree failed to typecheck: "+e.msg)
          debug("  in:\n"+showPosition(e.pos))
          None
      }
    } getOrElse {
      try {
        val typed = c.typecheck(shallowTree(tree))
        if (ascribedTree.nonEmpty && c.inferImplicitValue(typeOf[Warnings.`scrutinee type mismatch`.type]).isEmpty) {
          val expanded = unapply.get.tpe map (_.dealias)
          c.warning(c.enclosingPosition, s"""Scrutinee type: ${unapply.get.tpe}${
            if (expanded == unapply.get.tpe) ""
            else s"\n|  which expands to: $expanded"
          }
          |  seems incompatible with or is more specific than pattern type: Code[${typed.tpe}, _]${
            if (typeHoles.isEmpty) ""
            else s"\n|  perhaps one of the type holes (${typeHoles mkString ", "}) is unnecessary."
          }
          |Ascribe the scrutinee with ': Code[_,_]' or call '.erase' on it to remove this warning.""".stripMargin)
          // ^ TODO
        }
        typed -> typed.tpe
      } catch {
        case e: TypecheckException =>
          throw EmbeddingException.Typing(e.msg)
      }
    }
    
    scrutineeType foreach { asc =>
      debug(s"PROCESSING TYPE RELATION: $typedTreeType <:< ${asc}")
      def zip(lhs:Type,rhs:Type):Unit = (lhs.dealias,rhs.dealias) match {
        case (TypeRef(b0,s0,as0),TypeRef(b1,s1,as1)) if b0 =:= b1 && s0 == s1 => // TODO use baseType instead
          //debug((b0,s0,as0),(b1,s1,as1))
          as0.iterator zip as1.iterator foreach (zip _).tupled
        case _ =>
          debug(s"Subtyping knowledge: $lhs <:< $rhs")
          curTypeEqs += ((curCtxs.head, lhs, rhs))
      }
      zip(typedTreeType,asc)
    }
    
    val q"..$stmts; $finalTree" = typedTree
    
    // // For when traits are generated in a 'Traits' object:
    //val typeSymbols = (stmts collectFirst { case traits @ q"object Traits { ..$stmts }" =>
    //  stmts map { case t @ q"abstract trait ${name: TypeName} extends ..$_" =>
    //    debug("TRAITS",traits.symbol.typeSignature)
    //    (name: TypeName) -> internal.typeRef(traits.symbol.typeSignature, t.symbol, Nil) }
    //} get) toMap;
    val typeSymbols = stmts collect {
      // case t @ q"abstract trait ${name: TypeName} extends ..$_" => (name: TypeName) -> t.symbol
      case t @ q"object ${name: TermName} extends ..$_ { $_ => $tp }" => name.toTypeName -> tp.symbol
    } toMap;
    val holeSymbols = stmts collect {
      case t @ q"val ${name: TermName}: $_ = $_" => t.symbol
    } toSet;
    
    debug(s"Typed[${typedTreeType}]: "+finalTree)
    
    
    apply(Base, finalTree, termScope, config, unapply, 
      typeSymbols, holeSymbols, holes, splicedHoles, hopvHoles, termHoles, typeHoles, typedTree, typedTreeType, stmts, convNames, unquotedTypes)
    
  }
  
    
  
  
  
  
  
  
  
  
  def apply(
    baseTree: Tree, rawTree: c.Tree, termScopeParam: List[Type], config: QuasiConfig, unapply: Option[c.Tree],
    typeSymbols: Map[TypeName, Symbol], holeSymbols: Set[Symbol], 
    holes: Seq[Either[TermName,TypeName]], splicedHoles: collection.Set[TermName], hopvHoles: collection.Map[TermName,List[List[TermName]]],
    termHoles: Set[TermName], typeHoles: Set[TypeName], typedTree: Tree, typedTreeType: Type, stmts: List[Tree], 
    convNames: Set[TermName], unquotedTypes: Seq[(TypeName, Type, Tree)]
  ): c.Tree = {
    
    
    val shortBaseName = TermName("__b__")
    val Base = q"$shortBaseName"
    
    if (rawTree.tpe == null) throw EmbeddingException("Embedded tree has no type: "+showCode(rawTree))
    
    val retType = rawTree.tpe.widen // Widen to avoid too-specific types like Double(1.0), and be more in-line with Scala's normal behavior
    
    var termScope = termScopeParam // will contain the scope bases of all unquoted stuff + in xtion, possibly the scrutinee's scope
    // Note: in 'unapply' mode, termScope's last element should be the scrutinee's context
    
    var importedFreeVars = mutable.Map[String, Type]() // will contain the free vars imported by inserted IR's
    
    //type Context = List[TermSymbol]
    type Context = Map[TermName, Type]
    val termHoleInfo = mutable.Map[TermName, (Context, Type)]()
    
    /** Association between extracted binder names and the corresponding singleton types of the extracted variables (generated on the fly) */
    val extractedBinders = mutable.Map[TermName,Type]()
    
    // TODO aggregate these in a pre-analysis phase to get right hole/fv types...
    var freeVariableInstances = List.empty[(String, Type)]
    //var insertions = List.empty[(String, Tree)]
    // TODO
    //rawTree analyse {
    //  case q"$baseTree.$$[$tpt,$scp](..$idts)" => // TODO check baseTree
    //}
    // TODO see if we found the same holes as in `holes` !
    
    //val tree = rawTree transform { case q"$b.$$[$t,$c]($args: _*): _*" => q"$b.$$[$t,$c]($args: _*)" }
    val tree = rawTree
    
    
    val insertedTermTrees = mutable.ArrayBuffer[Tree]() // currently only used to disable caching if non-empty
    val insertedTypeTrees = mutable.Map[TermName,Tree]() // 'inserted types' are types that are explicitly unquoted or types for which an implicit is obtained
    insertedTypeTrees ++= unquotedTypes map { case (tn,tp,tpt) => c.freshName(tn.toTermName) -> q"$tpt.rep" }
    
    
    /** The _.Ctx types of the first-class variables bound so far (using first-class-variable insertion) */
    // Ideally this should be part of the implicit context ctx:Map[TermSymbol,Either[b.BoundVal,Type]]
    var boundScopes = Map.empty[TermSymbol,Type]
    def bindScope[R](scps: List[TermSymbol->Type])(k: => R) = {
      val old = boundScopes
      boundScopes ++= scps
      k alsoDo (boundScopes = old)
    }
    
    def freshSingletonVariableType(nam: TermName, typ: Type) = {
      /* Note: the following did not work:
           c.typecheck(q"object $nam extends $baseTree.Variable()(???); $nam").tpe
         because it creates a class symbol that can't be found  runtime (when a cast is inserted later in generated code) */
      c.typecheck(q"val $nam: $baseTree.Variable[$typ]{type OuterCtx=${termScope.last}} = ???; $nam:$nam.type").tpe
    }
    
    
    /** Embeds the type checked code with ModularEmbedding, but via the config.embed function, which may make the embedded
      * program go through an arbitrary base before ending up as Scala mirror code! */
    val codeTree = config.embed(c)(Base, baseTree.tpe, new BaseUser[c.type](c) {
      def apply(b: Base)(insert: (macroContext.Tree, Map[String, b.BoundVal]) => b.Rep): b.Rep = {
        
        
        val myBaseTree = baseTree
        object QTE extends QuasiTypeEmbedder[macroContext.type, b.type](macroContext, b, str => debug(str)) {
          val helper = QuasiEmbedder.this.Helpers
          //val baseTree: c.Tree = Base  // throws: scala.reflect.macros.TypecheckException: not found: value __b__
          val baseTree: c.Tree = myBaseTree
        }
        
        /** Special-cases the default modular embedding with quasiquote-specific details */
        object ME extends QTE.Impl {
          
          // Add to the type cache all the types that were explicitly inserted
          typeCache ++= unquotedTypes map {
            case (_,tp,tpt) => tp -> q"$tpt.rep".asInstanceOf[base.TypeRep]
          }
          // We could also make sure that there are no two inserted types corresponding to non-equivalent trees,
          // and raise a c.warning if it's the case, as it would likely be an error or potentially lead to surprises
          
          override def insertTypeEvidence(ev: base.TypeRep): base.TypeRep = if (unapply.isEmpty) ev else {
            val tn = c.freshName(TermName("insertedEv"))
            //debug(s"INS $tn -> $ev")
            insertedTypeTrees += tn -> ev.asInstanceOf[Tree]//FIXME
            Ident(tn).asInstanceOf[base.TypeRep]//FIXME
          }
          
          def holeName(nameTree: Tree, in: Tree) = nameTree match {
            case q"scala.Symbol.apply(${Literal(Constant(str: String))})" => str
            case _ => throw QuasiException("Free variable must have a static name, and be of the form: $$[Type]('name) or $$('name)\n\tin: "+showCode(in))
          }
          
          lazy val ExtractedBinder = typeOf[squid.lib.ExtractedBinder].typeSymbol
          
          override def liftTerm(x: Tree, parent: Tree, expectedType: Option[Type], inVarargsPos: Boolean)(implicit ctx: Map[TermSymbol, b.BoundVal]): b.Rep = {
          object HoleName { def unapply(tr: Tree) = Some(holeName(tr,x)) }
          x match {
              
              
            /** --- --- --- THIS REF --- --- --- */
            case This(tp) if !x.symbol.isModuleClass =>
              // Note: Passing `x.symbol.asType.toType` will still result in a path-dependent module type because of hole coercion
              val tree = q"$baseTree.$$$$[${TypeTree(x.tpe)}](scala.Symbol.apply(${s"$tp.this"}))"
              liftTerm(tree, parent, expectedType)
              
              
            /** This is to find repeated holes: $-less references to holes that were introduced somewhere else.
              * We convert them to proper hole calls and recurse. */
            case _ if holeSymbols(x.symbol) =>
              val tree = q"$baseTree.$$$$[${TypeTree(Nothing)}](scala.Symbol.apply(${x.symbol.name.toString}))"
              //debug("Repeated hole:",x,"->",tree)
              liftTerm(tree, parent, expectedType)
              
              
            /** Processes extracted binders in lambda parameters;
              * note: this is an adaptation of the implementation of lambdas in ModularEmbedding */
            case q"(..$ps) => $bo" =>
              
              // Processes extracted binders in lambda parameters
              val xtr = ps filter (_.symbol.annotations exists (_.tree.tpe.typeSymbol == ExtractedBinder))
              xtr foreach { vd =>
                val nam = vd.name
                val typ = vd.symbol.typeSignature
                val ltyp = liftType(typ)
                extractedBinders += (nam -> freshSingletonVariableType(nam,typ))
                debug("PARAM-BOUND HOLE:",nam,typ)
                assert(!termHoleInfo.contains(nam)) // Q: B/E necessary?
                termHoleInfo += nam -> (Map(nam -> typ) -> typ)
              }
              
              var cntxs = List.empty[TermSymbol->Type]
              
              val (params, bindings) = ps map {
                case p @ ValDef(mods, name, tpt, _) =>
                  traverseTypeTree(tpt)
                  val bv =
                    // inserted binders are marked with a name beginning with `$` – this allows the quasicode syntax `code{val $v = 0; $v + 1}`
                    if (name.toString.startsWith("$")) {
                      val n = name.toString.tail
                      val v = Ident(TermName(n))
                      val cntx = variableContext(v)
                      debug("INSERTED VAL:",n,cntx)
                      cntxs ::= p.symbol.asTerm -> cntx
                      val mb = b.asInstanceOf[(MetaBases{val u: c.universe.type})#MirrorBase with b.type]
                      mb.Existing(q"$v.`internal bound`").asInstanceOf[b.BoundVal]
                    }
                    else {
                      b.bindVal(name.toString, liftType(p.symbol.typeSignature), p.symbol.annotations map (a => liftAnnot(a, x)))
                    }
                  bv -> (p.symbol.asTerm -> bv)
              } unzip;
              
              val body = bindScope(cntxs) {
                liftTerm(bo, x, typeIfNotNothing(bo.tpe) orElse (expectedType flatMap FunctionType.unapply))(ctx ++ bindings)
              }
              b.lambda(params, body)
              
            /** Processes extracted binders in val bindings */
            case q"${vd @ ValDef(mods, TermName(name), tpt, rhs)}; ..$body" if vd.symbol.annotations exists (_.tree.tpe.typeSymbol == ExtractedBinder) =>
              val nam = TermName(name)
              
              val sign = vd.symbol.typeSignature
              val typ = if (mods.hasFlag(Flag.MUTABLE)) {
                val sym = typeOf[squid.lib.Var[Any]].typeSymbol
                internal.typeRef(typeOf[squid.lib.`package`.type], sym, sign :: Nil)
              }
              else sign
              
              val ltyp = liftType(typ)
              extractedBinders += (nam -> freshSingletonVariableType(nam,typ))
              
              debug("VAL-BOUND HOLE:",nam,typ)
              assert(!termHoleInfo.contains(nam)) // Q: B/E necessary?
              termHoleInfo += nam -> (Map(nam -> typ) -> typ)
              
              super.liftTerm(x, parent, expectedType, inVarargsPos)
              
            /** Processes inserted vals; adapted from ModularEmbedding */
            case q"${vdef @ ValDef(mods, TermName(name), tpt, rhs)}; ..$body" if name.startsWith("$") =>
              
              if (mods.hasFlag(Flag.MUTABLE)) throw QuasiException(
                "Insertion of symbol in place of mutable variables is not yet supported; " +
                  "explicitly use the squid.Var[T] data type instead", Some(vdef.pos))
              
              val n = name.toString.tail
              val v = Ident(TermName(n))
              val cntx = variableContext(v)
              
              debug("INSERTED VAL:",n,cntx)
              val mb = b.asInstanceOf[(MetaBases{val u: c.universe.type})#MirrorBase with b.type]
              val bound = mb.Existing(q"$v.`internal bound`").asInstanceOf[b.BoundVal]
              
              val value = liftTerm(rhs, x, typeIfNotNothing(vdef.symbol.typeSignature))
              
              val body2 = bindScope((vdef.symbol.asTerm -> cntx)::Nil) { liftTerm(
                setType( q"..$body",x.tpe ), // doing this kind of de/re-structuring loses the type
                x,
                expectedType
              )(ctx + (vdef.symbol.asTerm -> bound)) }
              
              b.letin(bound, value, body2, liftType(expectedType getOrElse x.tpe))
              
              
            case q"$baseTree.$$$$_var[$tpt]($v)" => // TODO remove this special mechanism?
              val ctx = variableContext(v)
              if (!boundScopes.valuesIterator.exists(_ =:= ctx)) termScope ::= ctx
              q"$v.rep".asInstanceOf[b.Rep]
              
              
            case q"$baseTree.$$Code[$tpt]($idt)" =>
              val tree = q"$baseTree.$$[$tpt,$Any]($idt.unsafe_asClosedCode)"
              liftTerm(tree, parent, expectedType)
              
            /** Replaces insertion unquotes with whatever `insert` feels like inserting.
              * In the default quasi config case, this will be the trees representing the inserted elements. */
            case q"$baseTree.$$[$tpt,$scp](..$idts)" => // TODO check baseTree:  //if base.tpe == Base.tpe => // TODO make that an xtor  // note: 'base equalsStructure Base' is too restrictive/syntactic
              //debug("UNQUOTE",idts)
              
              insertedTermTrees ++= idts
              
              val (bases, vars) = bases_variables(scp.tpe)
              
              val varsInScope = ctx map { case (sym, bv) => sym.name -> (sym.typeSignature -> bv) }
              
              val (captured,free) = vars mapSplit {
                case(n,t) => varsInScope get n match {
                  case Some((tpe,bv)) =>
                    tpe <:< t || ( throw EmbeddingException(
                      s"Captured variable `$n: $tpe` has incompatible type with free variable `$n: $t` " +
                        s"found in inserted code $$(${idts mkString ","})") )
                    Left(n, bv)
                  case None => Right(n, t)
                }
              } // TODO check correct free var types
              
              if (unapply.isEmpty) {
                // ^ we don't want to add free variables to the term's context requirement if we're in pattern mode
                // eg: in `case code"val x = 0; $tree" => ...`, though `tree` should capture `x` if `x` is free in it,
                // there is no reason to import other free variables/contexts from it
                
                termScope :::= bases.filterNot(b => boundScopes.valuesIterator.exists(_ =:= b)) // computes captured bases
                importedFreeVars ++= free.iterator map { case (n,t) => n.toString -> t }
              }
              
              def subs(ir: Tree) =
                insert(ir, captured.iterator map {case(n,bv) => n.toString->bv} toMap) // TODO also pass liftType(tpt.tpe)
              
              debug("Unquoting",s"$idts: Code[$tpt,$scp]", ";  env",varsInScope,";  capt",captured,";  free",free)
              
              // TODOmaybe: introduce a `splice` method in Base, get rid of SplicedHole, and make ArgsVararg smartly transform into ArgsVarargs when it sees a splice
              
              def assertVararg(t: Tree) = if (!inVarargsPos) throw QuasiException(s"Vararg splice unexpected in that position: ${showCode(t)}")
              idts match {
                case (idt @ q"$idts: _*") :: Nil =>
                  assertVararg(idt)
                  subs(idt)
                case idt :: Nil => subs(idt)
                case _ =>
                  assertVararg(q"$$(..$idts)")
                  subs(q"_root_.scala.Seq(..${idts}): _*")
              }
            
            /** Handles inserted references to variables symbols */
            case q"$baseTree.$$[$tvar]($v)" =>
              val tree = q"$baseTree.$$[$tvar,${Nothing}]($v.unsafe_asClosedCode)"
              /* ^ Note: Nothing needs to be inserted here as a proper type (not type tree), because the _.tpe will be queried by the recursive call */
              liftTerm(tree, parent, expectedType)
              
            case q"$baseTree.$$[$tfrom,$tto,$scp]($fun)" => // Special case for inserting staged IR functions
              val tree = q"$baseTree.$$[$tfrom => $tto,$scp]($baseTree.liftFun[$tfrom,$tto,$scp]($fun))"
              liftTerm(tree, parent, expectedType)
              
            case q"$baseTree.$$[$tfrom,$tto,$scp]($fun).apply($arg)" => // Special case for inserting staged IR functions that are immediately applied
              val tree = q"$baseTree.$$[$tfrom => $tto,$scp]($baseTree.liftFun[$tfrom,$tto,$scp]($fun))"
              val argl = liftTerm(arg, x, Some(tfrom.tpe)) // Q: use typeIfNotNothing?
              b.tryInline(liftTerm(tree, parent, expectedType), argl)(liftType(tfrom.tpe))
              
            case q"$baseTree.$$Code[$tfrom,$tto]($fun)" => // Special case for inserting staged Code functions
              val tree = q"$baseTree.$$Code[$tfrom => $tto]($baseTree.liftCodeFun[$tfrom,$tto]($fun))"
              liftTerm(tree, parent, expectedType)
              
            case q"$baseTree.$$Code[$tfrom,$tto]($fun).apply($arg)" => // Special case for inserting staged Code functions that are immediately applied
              val tree = q"$baseTree.$$Code[$tfrom => $tto]($baseTree.liftCodeFun[$tfrom,$tto]($fun))"
              val argl = liftTerm(arg, x, Some(tfrom.tpe)) // Q: use typeIfNotNothing?
              b.tryInline(liftTerm(tree, parent, expectedType), argl)(liftType(tfrom.tpe))
              
              
            // Note: For some extremely mysterious reason, c.typecheck does _not_ seem to always report type errors from terms annotated with `_*`
            case q"$baseTree.$$$$(scala.Symbol($stringNameTree))" => lastWords("Scala type checking problem.")
              
            case q"$baseTree.$$$$_*[$tp]($nameTree)" => // TODO check baseTree
              val name = holeName(nameTree, nameTree)
              val notSeqNothingExpectedType = expectedType map { et =>
                (et baseType typeOf[Seq[Any]].typeSymbol) match {
                  case TypeRef(_, _, tp :: Nil) =>
                    if (splicedHoles(TermName(name))) tp else { // no need to warn here as the warning will happen in case below (other handling of $$)
                      if (tp <:< Nothing) c.warning(c.enclosingPosition, s"Type inferred for vararg hole '$name' was Nothing. This is unlikely to be what you want.")
                      et
                    }
                  case NoType => throw QuasiException(s"The expected type of vararg hole '$name' should extend Seq[_], found `${et}`")
                }}
              liftTerm(q"$baseTree.$$$$[${TypeTree(Nothing)}]($nameTree)", parent, notSeqNothingExpectedType) // No need to pass `tp` as the type argument; it ensures there will be a warning if hole has no type
              
              
              
            /** Handling of the new new FV syntax: */
            
            // Correct usage of the `?` FV prefix
            case q"$baseTree.Predef.?.selectDynamic($nameTree)" => // TODO check baseTree
              val name = nameTree match { case Literal(Constant(str:String)) => str  case _ => 
                throw EmbeddingException("Free variable introduced with `?` should have a constant literal name.") }
              val tree = q"$baseTree.$$$$[${TypeTree(Nothing)}](scala.Symbol.apply(${name}))"
              liftTerm(tree, parent, expectedType)
            
            // Incorrect usage of the `?` FV prefix
            case q"$baseTree.Predef.?" if x.symbol.fullName == "squid.quasi.QuasiBase.Predef.$qmark" =>
              throw QuasiException("Unknown use of free variable syntax operator `?`.")
              
              
              
            /** Replaces calls to $$(name) with actual holes */
            case q"$baseTree.$$$$[$tpt]($nameTree)" => // TODO check baseTree
              
              val name = holeName(nameTree, x)
              
              val holeType = expectedType match {
                case None if tpt.tpe <:< Nothing => throw EmbeddingException(s"No type info for hole '$name'" + (
                  if (debug.debugOptionEnabled) s", in: $parent" else "" )) // TODO: check only after we have explored all repetitions of the hole? (not sure if possible)
                case Some(tp) =>
                  assert(!SCALA_REPEATED(tp.typeSymbol.fullName.toString))
                  
                  if (tp <:< Nothing) parent match {
                    case q"$_: $_" => // this hole is ascribed explicitly; the Nothing type must be desired
                    case _ => macroContext.warning(macroContext.enclosingPosition,
                      s"Type inferred for hole '$name' was Nothing. Ascribe the hole explicitly to remove this warning.") // TODO show real hole in its original form
                  }
                  
                  val mergedTp = if (tp <:< tpt.tpe || tpt.tpe <:< Nothing) tp else tpt.tpe
                  debug(s"[Hole '$name'] Expected",tp," required",tpt.tpe," merged",mergedTp)
                  
                  mergedTp
              }
              
              
              //if (splicedHoles(TermName(name))) throw EmbeddingException(s"Misplaced spliced hole: '$name'") // used to be: q"$Base.splicedHole[${_expectedType}](${name.toString})"
              
              val termName = TermName(name)
              
              // Note: there is no special logic about first-class variable symbols here because the logic happens later,
              // when computing the final types of extracted holes, where we distinguish whether the names bound in `ctx`
              // are extracted binders (and should therefore not correspond to a nominal context requirement)
              
              hopvHoles get TermName(name) match {
                case Some(idents) =>
                  
                  // TODO make sure HOPV holes withb the same name are not repeated? or at least have the same param types
                  // TODO handle HOPV holes in spliced position?
                  
                  val scp = ctx map { case k -> v => k.name -> (k -> v) }
                  val identVals = idents map (_ map scp)
                  val yes = identVals map (_ map (_._2))
                  val keys = idents.flatten.toSet
                  val no = scp.filterKeys(!keys(_)).values.map(_._2).toList  // Q: does `no` work correctly in the presence of extracted binders?
                  debug(s"HOPV: yes=$yes; no=$no")
                  val List(identVals2) = identVals // FIXME generalize
                  val hopvType = FunctionType(identVals2 map (_._1.typeSignature) : _*)(holeType)
                  termHoleInfo(termName) = Map() -> hopvType
                  b.hopHole(name, liftType(holeType), yes, no)
                  
                case _ =>
                  if (unapply isEmpty) {
                    debug(s"Free variable: $name: $tpt")
                    freeVariableInstances ::= name -> holeType
                    // TODO maybe aggregate glb type beforehand so we can pass the precise type here... could even pass the _same_ hole!
                  } else {
                    //val termName = TermName(name)
                    val scp = ctx.keys map (k => k.name -> k.typeSignature) toMap;
                    termHoleInfo(termName) = termHoleInfo get termName map { case (scp0, holeType0) =>
                      // We used to merge context variables present in both occurrences of the hole
                      //   (with: `val newScp = scp0 ++ scp.map { case (n,t) => n->glb(t :: scp0.getOrElse(n, Any) :: Nil) }`)
                      // But in fact, if a hole extracts the same tree in two different places, then it should NOT contain
                      // references to variables only in scope in one of these places! So we do an intersection here...
                      val newScp = scp.collect { case (n,t) if scp0 isDefinedAt n => n->lub(t :: scp0(n) :: Nil) }
                      newScp -> lub(holeType :: holeType0 :: Nil)
                    } getOrElse {
                      scp -> holeType
                    }
                  }
                  
                  if (splicedHoles(TermName(name)))
                       b.splicedHole(name, liftType(holeType))
                  else b.hole(name, liftType(holeType))
                  
              }
              
            /** Removes implicit conversions that were generated in order to apply the subtyping knowledge extracted from pattern matching */
            case q"${Ident(name:TermName)}.apply($x)" if convNames(name) => 
              liftTerm(x, parent, typeIfNotNothing(x.tpe))
              // ^ Q: correct to pass this expectedType? -- currently not passing through the current one 
              // because it would mean that sometimes the actual type is not a known subtype of the expected type...
              
            case _ => 
              //debug("NOPE",x)
              super.liftTerm(x, parent, expectedType)
          }}
          
          override def liftTypeUncached(tp: Type, wide: Boolean): b.TypeRep = {
            val tname = tp.typeSymbol.owner.name optionIf (ExtractedType unapply tp isDefined)
            // ^ in case of type hole t.Typ, the name we are looking for is no more the name of the type itself (Typ),
            // but the name of the owner (t). (The type itself used to be just 't' before.)
            tname flatMap (typeSymbols get _.toTypeName) filter (_ === tp.typeSymbol) map { sym =>
              b.typeHole(tname.get.toString)
            } getOrElse super.liftTypeUncached(tp, wide)
          }
          
        }
        ME(tree, Some(typedTreeType))
      }
    })
    
    
    //debug("Free variables instances: "+freeVariableInstances)
    val freeVariables = freeVariableInstances.groupBy(_._1).mapValues(_.unzip._2) map {
      case (name, typs) => name -> glb(typs)
    }
    if (freeVariables nonEmpty) debug("Free variables: "+freeVariables)
    
    if (termHoleInfo nonEmpty) debug("Term holes: "+termHoleInfo)
    
    
    //val expectedType = typeIfNotNothing(typedTreeType)
    //val res = c.untypecheck(lift(finalTree, finalTree, expectedType)(Map()))
    val res = c.untypecheck(codeTree)
    debug("Result: "+showCode(res))
    
    
    // We surrounds names with _underscores_ to avoid potential name clashes (with defs, for example)
    unapply match {
        
      case None =>
        
        // TODO check conflicts in contexts
        
        // Notes: we used to just compute `glb(termScope)`, but when quasiquotes have context `{}` (like `Const(42)`)
        // they introduce pesky AnyRef in the refined type; so now we make sure to remove it from the inferred context.
        // The reason `Const` returns an `IR[T,{}]` and not an `IR[T,Any]` is mostly historical/aesthetical, and is debatable
        val cleanedUpGLB = glb(termScope) |>=? {
          case RefinedType(typs,scp) => 
            //RefinedType(typs filterNot (AnyRef <:< _ ), scp)
            internal.refinedType(typs filterNot (AnyRef <:< _ ), scp)
        } |>=? { case glb if AnyRef <:< glb => Any }
        // To make things more consistent, we could say that `{}` is used whenever the context is empty, so we could 
        // replace `glb(termScope)` above with `glb(AnyRef :: termScope)`. But this causes problems down the line,
        // specifically when trying to use contravariance to use a context-free term with type IR[T,C] (where we _do not_ have `C <: AnyRef`)
        // producing errors like:
        //    error]  found   : BlockHelpers.this.IR[Unit,AnyRef]
        //    [error]  required: BlockHelpers.this.IR[Unit,C]
        
        if (termScope.size > 1) debug(s"Merging scopes; glb($termScope) = ${glb(termScope)} ~> $cleanedUpGLB")
        
        val ctxBase = tq"${cleanedUpGLB}"
        // Older comment:
        //val ctxBase = tq"${glb(termScope)}"
        // ^ Note: the natural empty context `{}` is actually equivalent to `AnyRef`, but `glb(Nil) == Any` so explicitly using
        // this empty context syntax can cause type mismatches. To solve this, we could do:
        //   val ctxBase = tq"${glb(AnyRef :: termScope)}"
        // But this makes some things uglier, like the need to have [C <: AnyRef] bounds so we don'r get IR[T,AnyRef with C{...}] types.
        // Instead, I opted for an implicit conversion IR[T,{}] ~> IR[T,Any] in the quasiquote Predef.
        
        // Old way:
        /*
        // putting every freevar in a different refinement (allows name redefinition!)
        val context = (freeVars ++ importedFreeVars).foldLeft(ctxBase){ //.foldLeft(tq"AnyRef": Tree){
          case (acc, (n,t)) => tq"$acc{val $n: $t}"
        }
        */
        
        // Note: an alternative would be to put these into two different refinements,
        // so we could end up with IR[_, C{val fv: Int}{val fv: Double}] -- which is supposedly equivalent to IR[_, C{val fv: Int with Double}]
        val fv = freeVariables ++ (importedFreeVars.iterator map {
          case (name, tpe) => name -> (freeVariables get name map (tpe2 => glb(tpe :: tpe2 :: Nil)) getOrElse tpe)
        })
        
        val context = tq"$ctxBase { ..${ fv map { case (n,t) => q"val ${TermName(n)}: $t" } } }"
        
        val tree = q"val $shortBaseName: $baseTree.type = $baseTree; $baseTree.`internal Code`[$retType, $context]($Base.wrapConstruct($res))"
        //                               ^ not using $Base shortcut here or it will show in the type of the generated term
        
        if (Any <:< cleanedUpGLB && fv.isEmpty) q"$tree:$baseTree.ClosedCode[$retType]" else tree
        
        
      case Some(selector) =>
        
        val termHoleInfoProcessed = termHoleInfo mapValues {
          case (scp, tp) =>
            val (nominalScp,symbolicScp) = scp.mapSplit {
              case(n,t) if extractedBinders.contains(n) => Right(tq"${extractedBinders(n)}#Ctx")
              case(n,t) => Left(n -> t)
            }
            val scpTyp = 
              CompoundTypeTree(Template(
                (termScope filterNot (Any <:< _) map typeToTree) ++ symbolicScp 
                  |>=? { case Nil => tq"$Any"::Nil }, // Scala typer doesn't seem to accept this being empty
                noSelfType, nominalScp map { case(n,t) => q"val $n: $t" } toList))
            (scpTyp, tp)
        }
        val termTypesToExtract = termHoleInfoProcessed map {
          case (name, (scpTyp, tp)) => name -> (
            if (splicedHoles(name)) tq"_root_.scala.collection.Seq[$baseTree.Code[$tp,$scpTyp]]"
            else if (extractedBinders.isDefinedAt(name)) tq"${extractedBinders(name)}"
            else tq"$baseTree.Code[$tp,$scpTyp]"
          )}
        val typeTypesToExtract = typeSymbols mapValues { sym => tq"$baseTree.CodeType[$sym]" }
        
        val extrTyps = holes.map {
          case Left(vname)  => termTypesToExtract.getOrElse(vname, lastWords(s"cannot find type info for term hole $vname"))
          case Right(tname) => typeTypesToExtract.getOrElse(tname, lastWords(s"cannot find type info for type hole $tname"))
        }
        debug("Extracted Types: "+extrTyps.map(showCode(_)).mkString(", "))
        
        val extrTuple = tq"(..$extrTyps)"
        //debug("Type to extract: "+extrTuple)
        
        val tupleConv = holes.map {
          case Left(name) if splicedHoles(name) =>
            val (scp, tp) = termHoleInfoProcessed(name)
            q"_maps_._3(${name.toString}) map (r => $Base.`internal Code`[$tp,$scp](r))"
          case Left(name) if extractedBinders isDefinedAt name =>
            val (scp, tp) = termHoleInfoProcessed(name)
            val tmp = TermName(c.freshName())
            q"""val $tmp = _maps_._1(${name.toString})  // the `rewrite` macro looks for this pattern and duplicating it would break it!
              $Base.Variable[$tp]($Base.extractVal($tmp)
              .getOrElse(throw new _root_.java.lang.AssertionError("Expected a variable symbol, got "+$tmp)))
              .asInstanceOf[${extractedBinders(name)}]"""
          case Left(name) =>
            //q"Quoted(_maps_._1(${name.toString})).asInstanceOf[${termTypesToExtract(name)}]"
            val (scp, tp) = termHoleInfoProcessed(name)
            q"$Base.`internal Code`[$tp,$scp](_maps_._1(${name.toString}))"
          case Right(name) =>
            //q"_maps_._2(${name.toString}).asInstanceOf[${typeTypesToExtract(name)}]"
            q"$Base.`internal CodeType`[${typeSymbols(name)}](_maps_._2(${name.toString}))"
        }
        
        val valKeys = termHoles.filterNot(splicedHoles).map(_.toString)
        val typKeys = typeHoles.map(_.toString)
        val splicedValKeys = splicedHoles.map(_.toString)
        
        
        //val termType = tq"$Base.Code[${typedTree.tpe}, ${termScope.last}]"
        // ^ We can't use the type inferred for the pattern or we'll get type errors with things like 'x.erase match { case ir"..." => }'
        val termType = tq"$Base.SomeCode"
        
        val typeInfo = q"type $$ExtractedType$$ = ${typedTree.tpe}" // Note: typedTreeType can be shadowed by a scrutinee type
        val contextInfo = q"type $$ExtractedContext$$ = ${termScope.last}" // Note: the last element of 'termScope' should be the scope of the scrutinee...
        //val contextInfo = q"type $$ExtractedContext$$ = ${glb(termScope)}" // Note: the last element of 'termScope' should be the scope of the scrutinee...
        
        
        // TODO also cache constructed reps?
        val wrappedRep = if (insertedTermTrees.isEmpty) {
          
          val uuid = java.util.UUID.randomUUID().toString()
          debug(s"Caching UUID: $uuid")
          debug(s"Inserted Types: $insertedTypeTrees")
          
          def fun = q"(..${ insertedTypeTrees map {case tn->tree => q"val $tn: $shortBaseName.TypeRep"} }) => $res"
          
          val gen = q"$Base.wrapExtract($shortBaseName.cacheRep($uuid,(..${
            insertedTypeTrees.unzip._2
          }), ${insertedTypeTrees.size match {
            case 0 => q"(_:Unit)=>$res"
            case 1 => fun
            case n => q"$fun.tupled"
          }}))"
          
          //debug("GEN "+gen)
          gen
          
        } else q"$Base.wrapExtract{..${ insertedTypeTrees map {case tn->tree => q"val $tn: $shortBaseName.TypeRep = $tree"} }; $res}"
        
        
        if (extrTyps.isEmpty) { // A particular case, where we have to make Scala understand we extract nothing at all
          
          q"""{
          val $shortBaseName: $baseTree.type = $baseTree
          new {
            $typeInfo
            $contextInfo
            def unapply(_t_ : $termType): Boolean = {
              //val $$shortBaseName = $$baseTree
              val _term_ = $wrappedRep
              $Base.extractRep(_term_, _t_.rep) match {
                case Some((vs, ts, fvs)) if vs.isEmpty && ts.isEmpty && fvs.isEmpty => true
                case Some((vs, ts, fvs)) => assert(false, "Expected no extracted objects, got values "+vs+", types "+ts+" and spliced values "+fvs); ???
                case None => false
              }
            }
          }}.unapply($selector)
          """
          
        } else {
          
          /* Scala seems to be fine with referring to traits which declarations do not appear in the final source code (they were typechecked with context `c`),
          but it seems to creates confusion in tools like IntelliJ IDEA (although it's not fatal).
          To avoid it, the typed trait definitions are spliced here */
          val typedTraits = stmts collect { case t @ q"abstract trait $_ extends ..$_" => t } //filter (_ => false)
          
          q"""{
          val $shortBaseName: $baseTree.type = $baseTree
          ..$typedTraits
          new {
            $typeInfo
            $contextInfo
            def unapply(_t_ : $termType): $scal.Option[$extrTuple] = {
              val _term_ = $wrappedRep
              $Base.extractRep(_term_, _t_.rep) map { _maps_0_ =>
                val _maps_ = $Base.`internal checkExtract`(${showPosition(c.enclosingPosition)}, _maps_0_)(..$valKeys)(..$typKeys)(..$splicedValKeys)
                (..$tupleConv)
              }
            }
          }}.unapply($selector)
          """
        }
        
    }
    
  }
    
  
  
  
  /** Creates a type tree from a Type, where all non-class types are replaced with existentials */
  def purgedTypeToTree(tpe: Type): Tree = {
    val existentials = mutable.Buffer[TypeName]()
    def rec(tpe: Type): Tree = tpe match {
      //case _ if !tpe.typeSymbol.isClass => //&& !(tpe <:< typeOf[Base.Param]) =>
        // FIXME?! had to change it to:   -- otherwise disgusting stuff happens with uninterpretedType[?0] etc.
      case _ if !tpe.typeSymbol.isClass && !tpe.typeSymbol.isParameter => //&& !(tpe <:< typeOf[Base.Param]) =>
        existentials += TypeName("?"+existentials.size)
        tq"${existentials.last}"
      case TypeRef(pre, sym, Nil) =>
        TypeTree(tpe)
      case TypeRef(pre, sym, args) =>
        AppliedTypeTree(Ident(sym.name),
          args map { x => rec(x) })
      case AnnotatedType(annotations, underlying) =>
        rec(underlying)
      case _ => TypeTree(tpe) // Note: not doing anything for other kinds of types, like ExistentialType...
    }
    val r = rec(tpe)
    val tpes = existentials map { tpn => q"type $tpn" }
    if (existentials.nonEmpty) tq"$r forSome { ..$tpes }" else r
  }
  
  
  def typeToTree(tpe: Type): Tree = {
    val r = tpe match {
      case TypeRef(pre, sym, Nil) =>
        TypeTree(tpe)
      case TypeRef(pre, sym, args) =>
        //AppliedTypeTree(Ident(sym.name),
        //  args map { x => typeToTree(x) })
        TypeTree(tpe)
      case AnnotatedType(annotations, underlying) =>
        typeToTree(underlying)
      case _ => TypeTree(tpe)
    }
    //println(s"typeToTree($tpe) = ${showCode(r)}")
    r
  }
  
  
  
}
