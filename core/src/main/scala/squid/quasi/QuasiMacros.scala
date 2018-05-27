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
import MacroUtils._
import utils.CollectionUtils._
import squid.lang.Base

import collection.mutable
import scala.reflect.macros.{blackbox, whitebox}
import scala.reflect.macros.runtime.AbortMacroException


object QuasiMacros {
  val deprecated_qqInterpolators = Set("ir", "dbg_ir")
  val qqInterpolators = deprecated_qqInterpolators ++ Set("code", "dbg_code", "c")
}
class QuasiMacros(override val c: whitebox.Context) extends QuasiBlackboxMacros(c)
class QuasiBlackboxMacros(val c: blackbox.Context) {
  import c.universe._
  import QuasiMacros._
  
  //val debug = { val mc = MacroDebugger(c); mc[NoDebug] } // always debug
  val debug = { val mc = MacroDebugger(c); mc[MacroDebug] } // will cut dbg unless MacroUtils.DebugLevel <: MacroDebug or the macro application symbol has @MacroSetting(debug = true)
  
  object Helpers extends {val uni: c.universe.type = c.universe} with meta.UniverseHelpers[c.universe.type] with ScopeAnalyser[c.universe.type]
  import Helpers._
  
  def mkConfig(Config: Type): QuasiConfig = {
    val ctor = Config.member(termNames.CONSTRUCTOR)
    
    if (NoSymbol === ctor)
      throw QuasiException(s"Could not find constructor on type $Config")
    
    if (ctor.alternatives.size =/= 1)
      throw QuasiException(s"More than one constructor on type $Config")
    
    // TODO check that ctor has unique param of 'whitebox.Context'
    
    val cm = srum.reflectClass(Config.typeSymbol.asClass.asInstanceOf[sru.ClassSymbol])
    val mm = cm.reflectConstructor(ctor.asMethod.asInstanceOf[sru.MethodSymbol])
    
    mm(c).asInstanceOf[QuasiConfig]
  }
  
  /** Generates a proper macro abort/error if a quasi or embedding exception is raised,
    * unless debugging is on (in which case it is often useful to see the stack trace) */
  def wrapError[T](code: => T): T = try code catch {
    case e: Throwable =>
      val err -> report -> pos = e match {
        case QuasiException(msg,pos) => "Quasiquote Error: "+msg -> true -> pos
        case EmbeddingException(msg) => "Embedding Error: "+msg -> true -> None
        case _:AbortMacroException => e.getMessage -> true -> None // don't emit warning when macro was explicitly aborted
        case e => e.getMessage -> false -> None
      }
      def getPos = pos.getOrElse(c.enclosingPosition).asInstanceOf[c.Position]
      if (debug.debugOptionEnabled) {
        debug("Macro failed with: "+e)
        //debug(e.getStackTrace mkString "\n")
        throw e
      }
      else if (report) c.abort(getPos, err)
      else {
        c.warning(getPos, "Macro failed with: "+e)
        throw e
      }
  }
  def wrapSymbolLoadingErrors[T](base: Base, code: => T): T = try code catch {
    case EmbeddingException(msg) =>
      c.abort(c.enclosingPosition, s"Embedding error: $msg")
    case base.TypSymbolLoadingException(fn,cause) =>
      c.abort(c.enclosingPosition, s"Could not access type symbol $fn. " +
        s"Perhaps it was defined in the same project, but should be compiled separately.")
    case base.MtdSymbolLoadingException(tp,sn,idx,cause) =>
      c.abort(c.enclosingPosition, s"Could not access method symbol $sn${idx.fold("")(":"+_)} in $tp.")
  }
  
  def deprecated(msg: String, since: String, disableOnImplicit: Type = NoType, warnInMacros: Bool = false) =
    if (disableOnImplicit == NoType || c.inferImplicitValue(disableOnImplicit).isEmpty)
    if (warnInMacros || !c.enclosingPosition.toString.startsWith("source-<macro>")) // don't warn if used within a macro (such as `assertCompiles`)
      c.warning(c.enclosingPosition, s"$msg (since $since)")
  
  lazy val `use of ir instead of code` = typeOf[Warnings.`use of ir instead of code`.type]
  
  def forward$(q: Tree*): Tree = c.macroApplication match {
    case q"$qc.$$[$t,$c](..$code)" => q"$qc.qcbase.$$[$t,$c](..$code)"
  }
  def forward$3(q: Tree): Tree = c.macroApplication match {
    case q"$qc.$$[$t]($vr)" => q"$qc.qcbase.$$[$t]($vr)"
  }
  def forward$$(name: Tree): Tree = {
    deprecated("The `$$[T]('x)` free variable syntax is deprecated; use syntax `(?x:T)` instead.", "0.2.0")
    c.macroApplication match {
      case q"$qc.$$$$[$t]($n)" => q"$qc.qcbase.$$$$[$t]($n)"
      case q"$qc.?[$t]($n)" => q"$qc.qcbase.$$$$[$t]($n)"
    }
  }
  
  def isQQInterpolators(str: String) = {
    if (deprecated_qqInterpolators(str)) 
      deprecated(s"Use the `code` quasiquote/quasicode interpolator instead of the deprecated `$str`.", "0.2.0", `use of ir instead of code`)
    qqInterpolators(str)
  }
  
  lazy val SubstituteVarargSym = typeOf[QuasiBase].member(TypeName("__*").encodedName)
  //lazy val SubstituteVarargSym = symbolOf[QuasiBase#__*] // nope: gets 'trait Seq' (dealias) ...
  
  /** Note: quasicode currently does not support inserted types, but it could in principle (though it would need another syntax). */
  def quasicodeImpl[Config: c.WeakTypeTag](tree: c.Tree) = wrapError {
    
    debug(s"Typed[${tree.tpe}]: "+showCode(tree))
    
    val quasiBase = c.macroApplication match {
      case x @ q"$qc.${id @ TermName(name)}[$tp]($code)" if isQQInterpolators(name) =>
        debug("Found quasicode base: "+qc)
        qc
    }
    val base = c.typecheck(q"$quasiBase.qcbase")
    
    val config = mkConfig(weakTypeOf[Config])
    
    val code = tree //transform { case q"$qc.$$[$typ,$ctx]($t)" =>  }
    //val code = tree transform { case q"$qc.$$[$typ,$ctx](..$xs)" if xs.size != 1 => ??? }
    
    object Embedder extends QuasiEmbedder[c.type](c)
    val res = Embedder(
      baseTree = base,
      rawTree = code,
      termScopeParam = Nil,
      config = config,
      unapply = None,
      typeSymbols = Map(),
      holeSymbols = Set(),
      holes = Seq(),
      splicedHoles = Set(),
      hopvHoles = Map(),
      termHoles = Set(),
      typeHoles = Set(),
      typedTree = code,
      typedTreeType = code.tpe,
      stmts = Nil,
      convNames = Set(),
      unquotedTypes = Seq()
    )
    
    debug("Generated:\n"+showCode(res))
    
    res: c.Tree
    //c.parse(showCode(res))
  }
  
  
  lazy val CodeTSym = symbolOf[QuasiBase#CodeType[_]]
  lazy val CodeSym = symbolOf[QuasiBase#Code[_,_]]
  lazy val AnyCodeSym = symbolOf[QuasiBase#AnyCode[_]]
  lazy val VariableSym = symbolOf[QuasiBase#Variable[_]]
  //lazy val VariableCtxSym = symbolOf[QuasiBase#Variable[Any]#Ctx] // doesn't seem to work!! – prints "free type Ctx"
  lazy val VariableCtxSym = typeOf[Base].member(TypeName("Variable")).asType.toType.member(TypeName("Ctx"))
  
  // TODO generalize to handle AnyCode and retrieve the path-dependent context type... (if well-defined/not existential!)
  def asCode(tp: Type, typeOfBase: Type) = tp.baseType(CodeSym) |>? {
    case TypeRef(typeOfBase0, CodeSym, typ :: ctx :: Nil) if typeOfBase =:= typeOfBase0 => (typ, ctx)
  }
  class AsCode(typeOfBase: Type) { def unapply(x:Type) = asCode(x, typeOfBase) }
  
  def asAnyCode(tp: Type, typeOfBase: Type) = tp.baseType(AnyCodeSym) |>? {
    case TypeRef(typeOfBase0, AnyCodeSym, typ :: Nil) if typeOfBase =:= typeOfBase0 => typ
  }
  class AsAnyCode(typeOfBase: Type) { def unapply(x:Type) = asAnyCode(x, typeOfBase) }
  
  def asVariable(tp: Type, typeOfBase: Type) = tp.baseType(VariableSym) |>? {
    case TypeRef(typeOfBase0, VariableSym, typ :: Nil) if typeOfBase =:= typeOfBase0 => typ
  }
  class AsVariable(typeOfBase: Type) { def unapply(x:Type) = asVariable(x, typeOfBase) }
  
  
  def unapplyImpl[L: c.WeakTypeTag](scrutinee: c.Tree) = wrapError {
    import c.universe._
    
    val quasiBase = c.macroApplication match {
      case x @ q"$base.QuasiContext(scala.StringContext.apply(..$_)).${id @ TermName(name)}.unapply($_)"
      if isQQInterpolators(name)
      =>
        debug("Found xtion base: "+base)
        base
    }
    
    val base = c.typecheck(q"$quasiBase.base")
    
    /** [INV:Quasi:reptyp]: we only match Code[_] types */
    // TODO if in contextual mode, nake sure IR terms are used!
    //
    //if (asIR(scrutinee.tpe, base.tpe).isEmpty) {
    //  throw EmbeddingException(s"Cannot match type `${scrutinee.tpe}`, which is not a proper subtype of `$base.${IRSym.name}[_,_]`"
    //    +"\n\tTry matching { case x: IR[_,_] => ... } first.")
    if (asAnyCode(scrutinee.tpe, base.tpe).isEmpty) {
      throw EmbeddingException(s"Cannot match type `${scrutinee.tpe}`, which is not a proper subtype of `$base.${AnyCodeSym.name}[_]`"
        +"\n\tTry matching { case x: Code[_] => ... } first.") // TODO add position: ..., Some(scrutinee.pos)
    }
    
    quasiquoteImpl[L](base, Some(scrutinee))
  }
  
  
  def applyImpl[Config: c.WeakTypeTag](inserted: c.Tree*) = wrapError {
    
    val quasiBase = c.macroApplication match {
      case x @ q"$base.QuasiContext(scala.StringContext.apply(..$_)).${id @ TermName(name)}.apply(..$_)"
      if isQQInterpolators(name)
      =>
        debug("Found ction base: "+base)
        base
    }
    
    val base = c.typecheck(q"$quasiBase.base")
    
    quasiquoteImpl[Config](base, None)
  }
  
  
  def quasiquoteImpl[Config: c.WeakTypeTag](base: Tree, scrutinee: Option[Tree]) = {
    
    val isUnapply = scrutinee.isDefined
    
    val config = mkConfig(weakTypeOf[Config])
    
    val builder = new quasi.PgrmBuilder[c.type](c)(isUnapply)
    
    var holes: List[(Either[TermName,TypeName], Tree)] = Nil // (Left(value-hole) | Right(type-hole), original-hole-tree)
    val splicedHoles = mutable.Set[TermName]()
    val hopvHoles = mutable.Map[TermName,List[List[TermName]]]()
    var typeBounds: List[(TypeName, EitherOrBoth[Tree,Tree])] = Nil
    
    // Keeps track of which holes still have not been found in the source code
    val remainingHoles = mutable.Set[TermName](builder.holes.keysIterator.toSeq: _*)
    
    var unquotedTypes = List[(TypeName, Type, Tree)]() // fresh name; type; type rep tree
    
    def unquoteType(name: TypeName, tp: Type, tree: Tree) = tp.baseType(CodeTSym) match {
      case TypeRef(tpbase,CodeTSym,tp::Nil) if tpbase =:= base.tpe =>
        unquotedTypes ::= ((name.toTypeName, tp, tree))
        tq"$tp"
      case TypeRef(_,_,_) => throw EmbeddingException(s"Cannot unquote type '$tp': it is not from base $base.")
      case _ => throw EmbeddingException(s"Cannot unquote type '$tp': it is not a CodeType[_].")
    }
    
    var hasStuckSemi = Option.empty[TermName]
    
    object AsCode extends AsCode(base.tpe)
    object AsAnyCode extends AsAnyCode(base.tpe)
    object AsVariable extends AsVariable(base.tpe)
    
    object AsVariableFun { def unapply(x:Type): Option[(Type,List[Symbol],Type,Type)] = x match {
      case AsFun(AsVariable(typ), AsCode(tr,ctxr)) => Some((typ,Nil,tr,ctxr))
      case AsFun(AsVariable(typ), ExistentialType(syms, AsCode(tr,ctxr))) => Some((typ,syms,tr,ctxr))
      case _ => None
    }}
    
    def mkTermHole(name: TermName, followedBySplice: Boolean) = {
      val h = builder.holes(name)
      assert(remainingHoles(name), s"Duplicated hole? $h")
      remainingHoles -= name
      
      //debug("HOLE: "+h)
      
      if (isUnapply) {
        
        val n = h.name filter (_.toString != "_") getOrElse c.freshName(TermName("ANON_HOLE")) toTermName;
        holes ::= Left(n) -> h.tree
        
        if (followedBySplice) {
          // This is to help Scala typecheck the spliced hole; 
          // if we don't and call $$ instead of $$_*, typechecking usually silently fails and makes <error> types, for some reason...
          q"$base.$$$$_*(${Symbol(n toString)}): _*"
        }
        else  {
          if (h.vararg) splicedHoles += n
          else h.tree match { case pq"$p @ __*" => splicedHoles += n   case _ => }
          if (splicedHoles(n)) q"$base.$$$$_*(${Symbol(n toString)}): _*"
          else
          q"$base.$$$$(${Symbol(n toString)})"
        }
        
      } else {
        h.tree match {
          //case t @ q"$_: _*" => q"$base.$$($t: _*)"  // not actually useful...
          case q"$t: _*" => q"$base.$$($t: _*)"
          //case q"$t: _*" => q"$base.$$($t: _*): _*" // Adding the _* so that typing does not think of this term as a Seq[T] (see vararg $'s type) -- EDIT: won't work, as ModEmb will interpret it as an object-language splice (which we don't want)
          case q"($t: $tp)" if (tp.tpe match { /** This is specifically for handling the {{{xs : __*}}} syntax (which is there as a complementary of the {{{xs @ __*}}} pattern) */
            case TypeRef(btp, sym, Nil) => (btp =:= base.tpe) && sym == SubstituteVarargSym
            case _ => false
          }) => q"$base.$$($t: _*)"
          case t if h.vararg => q"$base.$$($t: _*)"
            
          case t => 
            // Here we try to retrieve the Code type of the inserted code, so that we can generate a typed call to `$`
            // This is only necessary when we want a type coercion to happen during type checking of the shallow program;
            // (such as when we ascribe a term with a type and rely on pat-mat subtyping knowledge to apply the coercion)
            // if we don't do that, the expected type we want to coerce to will be propagated all the way inside the 
            // unquote, and the coercion would have to happen outside of the shallow program! (not generally possible)
            
            def checkIsBottom(ctx: Type) = if (!(ctx <:< Nothing))
              throw QuasiException("Only open code functions can benefit from automatic function lifting. " +
                s"Context `$ctx` is not Bottom, a.k.a Nothing.") // TODO "see doc"
            
            // We currently only handle auto-lifted functions of arities 1 to 3
            t.tpe match {
              case AsVariable(typ) => q"$base.$$$$_var($t)"
              // ^ Note: it's simpler to let QuasiEmbedder later figure out the exact context of the term (using its `variableContext` method)
              case AsCode(typ, ctx) => q"$base.$$[$typ,$ctx]($t)"
              case AsFun(AsCode(t0,ctx0), AsCode(tr,ctxr)) =>
                checkIsBottom(ctx0)
                q"$base.$$[$t0=>$tr,$ctxr]($base.liftOpenFun[$t0,$tr]($t))"
              case AsFun2(AsCode(t0,ctx0), AsCode(t1,ctx1), AsCode(tr,ctxr)) =>
                checkIsBottom(ctx0); checkIsBottom(ctx1)
                q"$base.$$[($t0,$t1)=>$tr,$ctxr]($base.liftOpenFun2[$t0,$t1,$tr]($t))"
              case AsFun3(AsCode(t0,ctx0), AsCode(t1,ctx1), AsCode(t2,ctx2), AsCode(tr,ctxr)) =>
                checkIsBottom(ctx0); checkIsBottom(ctx1); checkIsBottom(ctx2)
                q"$base.$$[($t0,$t1,$t2)=>$tr,$ctxr]($base.liftOpenFun3[$t0,$t1,$t2,$tr]($t))"
                
              case AsVariableFun(varTyp,existSyms,retTyp,retCtx) =>
                debug(s"Insertion of variable function with",varTyp,existSyms,retTyp,retCtx)
                t match {
                  case q"($x) => $body" =>
                    debug(s"Old context: $retCtx")
                    val (bs,vs) = bases_variables(retCtx)
                    // Remove from the context the existential symbol which correspond to the value bound in the lambda:
                    val newBases = bs.filterNot {
                      case TypeRef(vtp,VariableCtxSym,Nil) =>
                        //assert(existSyms contains vtp.typeSymbol)
                        // ^ not always true, as the body of an inserted variable function may not actually use its parameter!
                        existSyms.exists(v => x.symbol.owner === v.owner && v.name.toString === s"${x.symbol.name}.type")
                      case _ => false }
                    val ctx = mkContext(newBases, vs)
                    debug(s"New context: $ctx")
                    val t0 = c.parse(showCode(t))
                    /* ^ unfortunately, I couldn't find a way of doing this properly; the problem is that singleton
                         Variable types get broken, rainsing errors such as:
                             found   : VariableSymbolTests.this.DSL.Code[v.Typ,v.Ctx]
                                (which expands to)  VariableSymbolTests.this.DSL.Code[Int,v.Ctx]
                             required: VariableSymbolTests.this.DSL.Predef.Code[Int,v.Ctx]
                                (which expands to)  VariableSymbolTests.this.DSL.Code[Int,v.Ctx]
                         things I've tried independently and together:
                           - c.untypecheck(t)  – only changes when the problem occurs
                           - renewing every identifier in `t` with a fresh tree without symbol (`case Ident(n) => Ident(n)`)
                           - deeply transform the tree, setting the symbols or types to `null`
                     */
                    q"$base.$$$$_varFun[$varTyp,$retTyp,$ctx](${x.name})($t0)"
                  case _ => throw QuasiException("Inserted variable functions must be lambda expressions.", Some(t.pos))
                }
              case AsFun2(AsVariable(_),AsVariable(_), _) | AsFun3(AsVariable(_),AsVariable(_),AsVariable(_), _) =>
                throw QuasiException("Inserted variable functions are currently only supported for function arity 1.", Some(t.pos))
                
              case _ => 
                debug(s"Unrecognized insertion of type '${t.tpe}': ${t}\n –– typing may be imprecise as a result.")
                q"$base.$$($t)"
            }
            
        }
      }
    }
    
    val code = (builder.tree: Tree) transformRec( rec => {
      
      /** Note: value/parameters may be named "_", while anonymous function parameters are desugared to names of the form x$n
        * Anonymous function parameters are not a threat to soundness, so we do allow using them. */
      case ValDef(_, TermName(name), _, _) if isUnapply && (name == "_" /*|| (name startsWith "x$")*/) =>
        throw QuasiException("All matched bindings should be named.")
        
      /** Extracted/inserted binder: adds corresponding hole and an annotation to tell the IR and QuasiEmbedded to extract this binder */
      case ValDef(mods, name, tpt, rhs) if builder.holes.contains(name) =>
        val hole = builder.holes(name)
        if (isUnapply) {
          mkTermHole(name, false)
          val n = hole.tree match {
            case Bind(n, _) => n
            case _ => throw QuasiException(s"All extracted bindings must be named. In: $${${hole.tree}}", Some(hole.tree.pos))
          }
          val newMods = Modifiers(mods.flags, mods.privateWithin, q"new _root_.squid.lib.ExtractedBinder" :: mods.annotations)
          val r = ValDef(newMods, TermName(n.toString), rec(tpt), rec(rhs))
          r
        } else {
          //debug(s"INSERTED VAL: $hole : ${hole.tree.tpe} @ ${hole.tree.symbol}")
          assert(!hole.vararg)
          hole.tree.tpe match {
            case AsVariable(typ) =>
              remainingHoles -= name
              // we encode the tree in the name... unifying support for variable symbol insertion in quasiquotes with
              // variable symbol insertion in quasicode (which is done with syntax: code{val `$v` = 0; $(v)+1})
              val hname = TermName("$" + showCode(hole.tree))
              // Q: add annotation identifying the special inserted binder?
              if (tpt.isEmpty) ValDef(mods, hname, tq"$typ", rec(rhs))
              else ValDef(mods, hname, tpt, rec(rhs))
            case AsCode(typ, ctx) => throw QuasiException("Cannot insert a code value in place of a variable symbol.", Some(hole.tree.pos))
            case _ => throw QuasiException(s"Cannot insert object of type `${hole.tree.tpe}` here.", Some(hole.tree.pos))
          }
        }
        
      // This is to help Scala typecheck the spliced hole; if we don't and call $$ instead of $$_*, typechecking usually silently fails and makes <error> types, for some reason...
      case q"${Ident(name: TermName)}: _*" if isUnapply && builder.holes.contains(name) =>
        mkTermHole(name, true)
        
      case Ident(name: TermName) if builder.holes.contains(name) =>
        mkTermHole(name, false)
        
      // Identify and treat Higher-Order Pattern Variables (HOPV)
      case q"${Ident(name: TermName)}(...$argss)" if isUnapply && builder.holes.contains(name) =>
        val idents = argss map (_ map {
          case Ident(name:TermName) => name
          case e => throw EmbeddingException(s"Unexpected expression in higher-order pattern variable argument: ${showCode(e)}")
        })
        val hole = builder.holes(name)
        val n = hole.name filter (_.toString != "_") getOrElse (
          throw QuasiException("All higher-order holes should be named.", Some(hole.tree.pos)) // Q: necessary restriction?
        ) toTermName;
        hopvHoles += n -> idents
        mkTermHole(name, false)
        
      // Interprets bounds on extracted types, like in: `case List[$t where (Null <:< t <:< AnyRef)]`:
      case tq"${Ident(name: TypeName)} where $bounds" if isUnapply && builder.holes.contains(name.toTermName) =>
        val HoleName = builder.holes(name.toTermName).name.get.toTypeName // FIXME
        bounds match {
          case tq"$lb <:< ${Ident(HoleName)}"         => typeBounds ::= HoleName -> First (lb   )
          case tq"${Ident(HoleName)} <:< $ub"         => typeBounds ::= HoleName -> Second(   ub)
          case tq"$lb <:< ${Ident(HoleName)} <:< $ub" => typeBounds ::= HoleName -> Both  (lb,ub)
          case _ => throw QuasiException(s"Illegal bounds specification shape: `${showCode(bounds)}`. " +
            s"It shoule be of the form: `LB <:< $HoleName` or `$HoleName <:< UB` or `LB <:< $HoleName <:< UB`.")
        }
        rec(Ident(name))
        
      case Ident(name: TypeName) if builder.holes.contains(name.toTermName) => // in case we have a hole in type position ('name' is a TypeName but 'holes' only uses TermNames)
        val hole = builder.holes(name.toTermName)
        remainingHoles -= name.toTermName
        if (hole.vararg) throw EmbeddingException(s"Varargs are not supported in type position.${showPosition(hole.tree.pos)}") // (for hole '${hole.tree}').")
        
        if (isUnapply) {
          val n = hole.name.filter(_.toString != "_")
            .getOrElse(throw QuasiException("All extracted types should be named.", Some(hole.tree.pos))).toTypeName // TODO B/E // TODO relax?
          holes ::= Right(n) -> hole.tree
          tq"$n"
        }
        else { // !isUnapply
          unquoteType(name.toTypeName, hole.tree.tpe, hole.tree)
        }
        
      //case t @ q"$$(..$args)" if unapply => throw EmbeddingException(s"Unsupported alternative unquoting syntax in unapply position: '$t'")
      case t @ q"$$(..$args)" => // alternative unquote syntax
        q"$base.$$(..$args)"
        // ^ TODO remove this syntax
        
      case t @ q"${Ident(tn: TermName)}?" => // better FV syntax, old version
        deprecated("The `x?` free variable syntax is deprecated; use syntax `?x` instead.", "0.2.0")
        if (!isUnapply) {
          holes ::= Left(tn) -> q"$tn" // holes in apply mode are interpreted as free variables
        }
        q"$base.$$$$(${Symbol(tn.toString)})"
        
      // Special case for when the question mark is stuck to a semicolon... as in ir"x?:Int"
      // Unfortunately, there is not much we can soundly do as the argument has been parsed as a term, not a type.
      // So we showCode it and reparse it as a type...
      case t @ q"${id @ Ident(tn: TermName)} ?: $wannabeType" =>
        hasStuckSemi = Some(tn)
        try rec(c.parse(s"$tn ? : "+showCode(wannabeType))) catch {
          case scala.reflect.macros.ParseException(pos, msg) => builder.parseError(msg)
        }
        
        
      case t @ Ident(name: TermName) if name.decodedName.toString.startsWith("$") => // escaped unquote syntax
        //q"open(${name.toString})"
        val bareName = name.toString.tail
        if (bareName.isEmpty) throw EmbeddingException(s"Empty escaped unquote name: '$$$t'")
        
        if (isUnapply) {
          q"$base.$$(${TermName(bareName)})" // escaped unquote in unapply mode does a normal unquote
        }
        else { // !isUnapply
          deprecated("The `$$x` free variable syntax is deprecated; use syntax `?x` instead.", "0.2.0")
          val tn = TermName(bareName)
          holes ::= Left(tn) -> q"$tn" // holes in apply mode are interpreted as free variables
          q"$base.$$$$(${Symbol(bareName)})"
        }
        
      case t @ Ident(name: TypeName) if name.decodedName.toString.startsWith("$") => // escaped type unquote syntax
        val bareName = name.toString.tail
        if (isUnapply) {
          // Note: here we want a type unquote, not a type hole!
          
          val typedTypeRef = c.typecheck(Ident(TermName(bareName)))
          unquoteType(TypeName(bareName), typedTypeRef.tpe, c.untypecheck(typedTypeRef))
          
        } else {
          throw EmbeddingException(s"Free type variables are not supported: '$$$t'")
        }
        
    })
    if (remainingHoles nonEmpty) {
      val missing = remainingHoles map builder.holes map (h => (h.name map ("$"+_) getOrElse s"$${${showCode(h.tree)}}", h.tree.pos))
      // ^ Not displaying the tree when possible, because in apply mode, typechecked trees can be pretty ugly...
      
      throw QuasiException(
        s"Illegal hole position${if (missing.size > 1) "s" else ""} for: "+missing.map(_._1).mkString(", "),
        Some(missing.head._2)
      )
    }
    
    object Embedder extends QuasiEmbedder[c.type](c)
    val res = try Embedder.applyQQ(base, code, holes.reverse map (_._1), splicedHoles, hopvHoles, typeBounds.toMap, unquotedTypes, scrutinee, config)
    catch {
      case e: EmbeddingException if hasStuckSemi.isDefined => 
        c.warning(c.enclosingPosition, s"It seems you tried to annotate free variable `${hasStuckSemi.get}` with `:`, " +
          "which may have been interpreted as operator `?:` -- " +
          "use a space to remove this ambiguity.")
        throw e
    }
    
    debug("Generated:\n"+showCode(res))
    
    res: c.Tree
    //c.parse(showCode(res)): c.Tree
  }
  
  
  
  def implicitTypeImpl[Config: c.WeakTypeTag, T: c.WeakTypeTag] = wrapError {
    val T = weakTypeOf[T]
    
    debug("Implicit for "+T)
    
    val config = mkConfig(weakTypeOf[Config])
    
    val quasiBase = c.macroApplication match {
      case q"$qc.dbg.implicitType[$tp]" =>
        debug("Found implicitType base: "+qc)
        qc
      case q"$qc.implicitType[$tp]" =>
        debug("Found implicitType base: "+qc)
        qc
    }
    val myBaseTree = c.typecheck(q"$quasiBase.base")
    
    val codeTree = config.embed(c)(myBaseTree, myBaseTree.tpe, new BaseUser[c.type](c) {
      def apply(b: Base)(insert: (macroContext.Tree, Map[String, b.BoundVal]) => b.Rep): b.Rep = {
        object QTE extends QuasiTypeEmbedder[macroContext.type, b.type](macroContext, b, str => debug(str)) {
          val helper = QuasiBlackboxMacros.this.Helpers
          val baseTree = myBaseTree
          //def freshName(hint: String): TermName = TermName(c.freshName(hint))
        }
        object ME extends QTE.Impl
        ME.liftType(T).asInstanceOf[b.Rep] // TODO proper way to do that!
      }
    })
    
    val res = q"$myBaseTree.`internal CodeType`[$T]($codeTree)"
    
    debug("Generated: "+showCode(res))
    //if (debug.debugOptionEnabled) debug("Of Type: "+c.typecheck(res).tpe) // Makes a StackOverflow when type evidence macro stuff happen
    
    //codeTree: c.Tree
    res
  }
  
  
  def varSubsImpl[C: c.WeakTypeTag](term: c.Tree) = {
    import c.universe._
    
    val (base -> quoted, fv, typ -> ctx, termCtx) = c.macroApplication match {
      case q"$b.IntermediateCodeOps[$t,$c]($q).${TermName("apply"|"subs")}[$_]($v)~>[$tc]($_)" => (b -> q, v, t.tpe -> c.tpe, tc.tpe)
      case q"$b.IntermediateCodeOps[$t,$c]($q).${TermName("apply"|"subs")}[$_]($v).dbg_~>[$tc]($_)" => (b -> q, v, t.tpe -> c.tpe, tc.tpe)
    }
    
    val C = termCtx // weakTypeOf[C] is not useful as it returns a tag of C as viewed from the definition of ~> !!
    
    if (!fv.symbol.asTerm.isStable) c.abort(fv.pos, s"Cannot substitute variable '$fv', not a stable path.")
    
    object QE extends QuasiEmbedder[c.type](c)
    val fvCtx = QE.variableContext(fv)
    
    val (bases, vars) = bases_variables(ctx)
    
    val outputCtx = {
      val (cbases, cvars) = bases_variables(C)
      val newBases = bases collect { case b if !(b =:= fvCtx) => b }
      if (newBases.size === bases.size)
      if (!(ctx <:< Nothing)) // if context is bottom, we're dealing with an explicit OpenCode, where it's understood
                              // that we don't care about contexts (so there's nothing to safeguard here)
        c.abort(c.enclosingPosition, s"Term of context '$ctx' does not seem to have free variable '$fv' to substitute.")
      debug(s"$bases ~> $newBases")
      mkContext(cbases ::: newBases, vars ::: cvars)
    }
    
    debug(s"Output context: $outputCtx")
    
    val sanitizedTerm =
      if (debug.debugOptionEnabled) term else untypeTreeShape(c.untypecheck(term))
    
    val res = q"${c.untypecheck(fv)}.substitute[$typ,$outputCtx]($quoted,$sanitizedTerm)"
    
    debug("Generated: "+showCode(res))
    
    res
  }
  
  def subsImpl[T: c.WeakTypeTag, C: c.WeakTypeTag](s: c.Tree) = {
    import c.universe._
    
    val T = weakTypeOf[T]
    val C = weakTypeOf[C]
    
    val (base -> quoted, typ -> ctx) = c.macroApplication match {
      case q"$b.IntermediateCodeOps[$t,$c]($q).subs[$_,$_]($_)" => (b -> q, t.tpe -> c.tpe)
      case q"$b.IntermediateCodeOps[$t,$c]($q).dbg_subs[$_,$_]($_)" => (b -> q, t.tpe -> c.tpe)
    }
    
    val name -> term = s match {
      case q"scala.this.Predef.ArrowAssoc[$_](scala.Symbol.apply(${Literal(Constant(name: String))})).->[$_]($term)" =>
        name -> term
      // In Scala 2.12, we don't get the weird `this` anymore:
      case q"scala.Predef.ArrowAssoc[$_](scala.Symbol.apply(${Literal(Constant(name: String))})).->[$_]($term)" =>
        name -> term
      case _ => c.abort(s.pos, s"Illegal syntax for `subs`; Expected: `term0.subs 'name -> term1`, found: `${showCode(s)}`")
    }
    
    //debug(name, term)
    
    val (bases, vars) = bases_variables(ctx)
    
    val replacedVarTyp = vars find (_._1.toString === name) getOrElse
      c.abort(c.enclosingPosition, s"This term does not have a free variable named '$name' to substitute.") _2;
    
    if (!(T <:< replacedVarTyp)) c.abort(term.pos, s"Cannot substitute free variable `$name: $replacedVarTyp` with term of type `$T`")
    
    val outputCtx = {
      val (cbases, cvars) = bases_variables(C)
      mkContext(cbases ::: bases, (vars filter (_._1.toString =/= name)) ::: cvars)
    }
    
    debug(s"Output context: $outputCtx")
    
    val sanitizedTerm =
      if (debug.debugOptionEnabled) term else untypeTreeShape(c.untypecheck(term))
      //term
      //c.untypecheck(term)
    val res = q"$base.`internal Code`[$typ,$outputCtx]($base.substituteLazy($quoted.rep, Map($name -> (() => ($sanitizedTerm:$base.Code[_,_]).rep))))"
    
    debug("Generated: "+showCode(res))
    
    res
  }
  
  
  
}
