package squid
package quasi

import utils._
import squid.lang.Base

/* TODO: make it work with intermediate bases (eg: `ViaASTQuasiConfig`) */
abstract class QuasiTypeEmbedder[C <: scala.reflect.macros.whitebox.Context, B <: Base](val c: C, val base: B, debug: String => Unit) {
  import c.universe._
  
  val helper: meta.UniverseHelpers[c.universe.type]
  import helper._
  
  val baseTree: Tree
  
  class Impl extends ModularEmbedding[c.universe.type, B](c.universe, base, debug) {
    
    def insertTypeEvidence(ev: base.TypeRep): base.TypeRep = ev
    
    override def unknownTypefallBack(tp: Type): base.TypeRep = {
      
      debug(s"Lifting unknown type $tp (${tp.widen.dealias})")
      
      if (tp.widen =:= ExtrudedType || tp.widen.contains(ExtrudedType.typeSymbol)) { // was: contains(symbolOf[QuasiBase.`<extruded type>`])
        debug(s"Detected widened type hole: ${tp.widen}")
        val purged = tp.toString.replaceAll(ExtrudedType.toString, "<extruded type>")
        throw EmbeddingException(s"Precise info for extracted type was lost, " +
          s"possibly because it was extruded from its defining scope " +
          s"or because the least upper bound was obtained from two extracted types, in: $purged")
      }
      
      
      val irType = c.typecheck(tq"$baseTree.CodeType[$tp]", c.TYPEmode) // TODO use internal.typeRef
      debug(s"Searching for an `$irType` implicit")
      c.inferImplicitValue(irType.tpe, withMacrosDisabled = true) match {
        case EmptyTree =>
        case impt =>
          debug(s"Found: "+showCode(impt))
          return (q"$impt.rep".asInstanceOf[base.TypeRep] // FIXME
            |> insertTypeEvidence)
      }
      
      val vals = c.asInstanceOf[reflect.macros.runtime.Context].callsiteTyper.context.enclosingContextChain.flatMap {
        _.scope collect {
          case sym if sym.isVal
            && sym.isInitialized // If we look into the type of value being constructed (eg `val x = exp"42"`),
                                 // it will trigger a 'recursive value needs type' error
            //&& sym.name.toString == tp.typeSymbol.name.toString // used to compare names directly, but sometimes failed because they came from different cakes...
          =>
            sym -> sym.tpe.dealias // dealiasing so for example base.Predef.IR[_,_] ~> base.IR[_,_]
        }
      }.asInstanceOf[List[(TermSymbol, Type)]]
      
      val QTSym = symbolOf[QuasiBase#CodeType[_]]
      
      //val PredefQTSym = symbolOf[QuasiBase#Predef[_ <: QuasiConfig]#CodeType[_]]
      //val PredefQTSym = typeOf[QuasiBase#Predef[_ <: QuasiConfig]#CodeType[_]].typeSymbol
      // ^ For some reson, these always return a symbol s where s.fullName == "squid.quasi.QuasiBase.CodeType"
      
      vals foreach {
        case (sym, TypeRef(tpbase, QTSym /*| PredefQTSym*/, tp0::Nil)) 
          if tpbase =:= baseTree.tpe 
          && tp0 <:< tp && tp <:< tp0 // NOTE: for some godforsaken reason, sometimes in Scala this is not the same as `tp0 =:= tp`
          // For example in  {{{ (typs:List[CodeType[_]]) map { case typ: CodeType[t] => dbg.implicitType[t] } }}}
        =>
          debug("FOUND QUOTED TYPE "+sym)
          return (q"$sym.rep".asInstanceOf[base.TypeRep] // FIXME
            |> insertTypeEvidence)
        //case (sym, TypeRef(tpbase, QTSym, tp::Nil)) =>
        //  debug(s"Note: $tpbase =/= ${baseTree.tpe}")
        //case (sym, TypeRef(tpbase, qtsym, tp::Nil)) =>
        //  debug(s"$qtsym ${qtsym.fullName} ${PredefQTSym.fullName} ${QTSym.fullName} ${qtsym == PredefQTSym}")
        case _ =>
      }
      
      
      if (tp <:< ExtrudedType && !(tp <:< Null) // Note that: tp <:< Nothing ==> tp <:< Null so no need for the test
          || ExtractedType.unapply(tp).nonEmpty) {
        
        throw EmbeddingException(s"Could not find type evidence associated with extracted type `$tp`.")
        
      } else {
        
        val tagType = c.typecheck(tq"_root_.scala.reflect.runtime.universe.TypeTag[$tp]", c.TYPEmode)
        
        c.inferImplicitValue(tagType.tpe) match {
          case EmptyTree =>

            if (tp.typeSymbol == symbolOf[Array[_]]) {
              // Note: srum.runtimeClass(sru.typeOf[Array[Int]]).toString == [I
              throw EmbeddingException.Unsupported("Arrays of unresolved type.")
            }

            throw EmbeddingException(s"Unknown type `$tp` does not have a TypeTag to embed it as uninterpreted.")
            
          case impt =>
            
            // We used to do the following, which helped to let-bind (using the caching mechanism of `ModularEmbedding`,
            // since this would call the base's `uninterpretedType`). However, now `uninterpretedType` is overridden and
            // inserted types are aggregated and named, so that caching can index on them, so this is no more necessary:
            /*
            // Note: not using `impt`! cf. below... (we just ensure it exists to give the better error message above)
            super.unknownTypefallBack(tp) // unnecessary, as it just generates a call to uninterpretedType without the implicit resolved
            // ^ actually useful to cache the tag!
            */
            
            q"$baseTree.uninterpretedType($impt)".asInstanceOf[base.TypeRep] |> insertTypeEvidence
            
            // Older:
            /* Does not help, as it bypasses the underlying base:
             * although the tree creation is cached, it will NOT get let-bound, and will be duplicated all over the place */
            //return typeCache.getOrElseUpdate(tp, q"$baseTree.uninterpretedType[$tp]($impt)".asInstanceOf[base.TypeRep])
            
        }
        
      }
      
      
      
      
      
    }
    
  }
  
  
}
