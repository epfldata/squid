// Copyright 2019 EPFL DATA Lab (data.epfl.ch)
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

import squid.utils._
import squid.utils.MacroUtils.MacroSetting

import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly
import scala.reflect.macros.whitebox
import scala.language.experimental.macros

/** Lifts a class and/or object definitions, so that it can be processed using Squid.
  * When a class is annotated with @lift, a method called `reflect` is created in the companion object, which accepts
  * a squid.lang.Definitions d and returns a squid.lang.Definitions.TopLevel.ClassOrObject[_] instance. */
@compileTimeOnly("Enable macro paradise to expand macro annotations.")
class lift extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro ClassLifting.liftAnnotImpl
}
object lift {
  def thisClass(d: squid.lang.Definitions): Any = macro ClassLifting.classLiftImpl
}
@compileTimeOnly("Enable macro paradise to expand macro annotations.")
class dbg_lift extends StaticAnnotation {
  @MacroSetting(debug = true) def macroTransform(annottees: Any*): Any = macro ClassLifting.liftAnnotImpl
}
object dbg_lift {
  @MacroSetting(debug = true) def thisClass(d: squid.lang.Definitions): Any = macro ClassLifting.classLiftImpl
}

// no @compileTimeOnly annotation because this is currently not removed by @embed
class doNotLift extends StaticAnnotation

/*
  TODO: handle
    - inherited parents
    - generic classes
    - nested classes
    - class and object constructors
    - val/var parameters
    - doNotLift
  TODO: cache generated symbols! (is it already done?)
*/
class ClassLifting(override val c: whitebox.Context) extends QuasiMacros(c) {
  import c.universe._
  
  def req(cnd: Bool, msg: => String): Unit = if (!cnd) reqFail(msg)
  def reqFail(msg: String): Nothing = throw new EmbeddingException(msg)
  
  def liftAnnotImpl(annottees: c.Tree*): c.Tree = wrapError {
    
    def reflectDef(tp: Tree) =
      q"def reflect(defs: _root_.squid.lang.Definitions): $tp = ${
        if (debug.debugOptionEnabled) q"dbg_lift" else q"lift"
      }.thisClass(defs)"
    
    annottees match {
      case (cls: ClassDef) :: Nil =>
        // TODO Conceptually should be a ClassWithoutObject...
        //      to do that we need to mark the synthetic object so it's not lifted
        q"$cls; object ${cls.name.toTermName} { ${reflectDef(tq"defs.TopLevel.ClassWithObject[${cls.name}]")} }"
      case (cls: ClassDef) :: (obj: ModuleDef) :: Nil =>
        q"$cls; ${ModuleDef(obj.mods, obj.name,
          Template(obj.impl.parents, obj.impl.self, obj.impl.body :+
            reflectDef(tq"defs.TopLevel.ClassWithObject[${cls.name}]")))}"
      case (obj: ModuleDef) :: Nil =>
        q"${ModuleDef(obj.mods, obj.name,
          Template(obj.impl.parents, obj.impl.self, obj.impl.body :+ 
            reflectDef(tq"defs.TopLevel.ObjectWithoutClass[${obj.name}.type]")))}"
      case _ => reqFail("The lifted definition must be a class or an object.")
    }
  }
  
  def classLiftImpl(d: c.Tree): c.Tree = wrapError {
    val c2 = c.asInstanceOf[scala.reflect.macros.contexts.Context]
    val pack = c2.enclosingPackage.asInstanceOf[PackageDef]
    val obj = c2.enclosingClass.asInstanceOf[Tree] match {
      case md: ModuleDef => md
      case _ => reqFail("The class lifting macro should be placed within the companion object of the lifted class.")
    }
    req(obj.symbol.owner.isPackage, "Can only lift top-level definitions.")
    /*
<<<<<<< HEAD
    val pack2 = new Transformer {
      override def transform(tree: Tree) = tree match {
          
=======
    debug(s"############ Lifting ${obj.symbol} ############")
    val pack2 = new Transformer {
      override def transform(tree: Tree) = tree match {
          
        case cd @ (_: ClassDef | _: ModuleDef) if !obj.symbol.fullName.startsWith(cd.symbol.fullName) =>
          debug(s"Ignoring ${cd.symbol.fullName} =/= ${obj.symbol.fullName}")
          q""
          
>>>>>>> WIP
        // The goal of the following was to remove references to the macro call and the macro annotation...
        // Unfortunately, while these _seem_ to achieve their purpose I, could not prevent recursive execution of
        // the macro in certain cases. It's not clear why.
        // So I simply disabled macros in the typecheck call below instead (see  `withMacrosDisabled = true`).
        /*
        case q"$_.thisClass($_)" => q"???"
        case md: ModuleDef =>
          internal.setSymbol(
          ModuleDef(Modifiers(md.mods.flags, md.mods.privateWithin, Nil), md.name, 
            transform(md.impl).asInstanceOf[Template])
            , md.symbol)
        case md: ClassDef =>
          internal.setSymbol(
          ClassDef(Modifiers(md.mods.flags, md.mods.privateWithin, Nil), md.name, md.tparams,
            transform(md.impl).asInstanceOf[Template])
            , md.symbol)
        */
          
        case _ => super.transform(tree)
      }
    } transform pack
    */
    val pack2 = internal.setSymbol(
      PackageDef(pack.pid, pack.stats.collect {
      case cd @ (_: ClassDef | _: ModuleDef) if obj.symbol.fullName === cd.symbol.fullName => cd
    }), pack.symbol)
    
    //val tpack = c.typecheck(pack2).asInstanceOf[PackageDef]
    val tpack = c.typecheck(pack2, withMacrosDisabled = true).asInstanceOf[PackageDef]
    //debug(s"Typed: ${showCode(tpack)}")
    debug(s"Typed: ${tpack}")
    
    val (tobj,tcls) = {
      val objs = tpack.stats.collect{ case md: ModuleDef => md }
      assert(objs.size == 1)
      val clss = tpack.stats.collect{ case cd: ClassDef => cd }
      assert(clss.size <= 1)
      (objs.head, clss.headOption)
    }
    
    object MBM extends MetaBases {
      val u: c.universe.type = c.universe
      def freshName(hint: String) = c.freshName(TermName(hint))
    }
    val dnme = d match {
      case Ident(nme: TermName) => nme
      case _ => reqFail("")
    }
    
    // This is to work around strange scalac inconsistencies with the treatment of path-dependent types
    val td = c.typecheck(q"$dnme: $dnme.type")
    internal.setType(d, td.tpe)
    
    val Base = new MBM.MirrorBase(d, Some(td.tpe))
    class MEBase extends ModularEmbedding[c.universe.type, Base.type](c.universe, Base, str => debug(str))
    
    def liftTemplate(name: Name, templ: Template, self: Tree, sign: Type): (List[Tree], List[Tree]) = {
      debug(s"###### Lifting $name ######")
      debug(s"Signature: ${sign}")
      
      val methods = templ.body.collect {
        case md: DefDef
          if (md.symbol =/= c2.enclosingMethod.symbol.asInstanceOf[Symbol]) // avoid lifting the `reflect` method itself
          && (md.name =/= termNames.CONSTRUCTOR)
          && !md.symbol.asMethod.isAccessor // accessors are SOMETIMES(!!) generated for class fields at this point
        =>
          debug(s"====== Lifting ${md.symbol} ======")
          
          object ME extends MEBase {
            lazy val tparams = md.symbol.typeSignature.typeParams.map{tp =>
              assert(tp.asType.typeParams.isEmpty)
              tp -> Base.typeParam(tp.name.toString)}
            lazy val vparams = md.symbol.typeSignature.paramLists.map(vps =>
              vps.map{vp =>
                vp -> Base.bindVal(vp.name.toString, ME.liftType(vp.typeSignature), Nil)})
            override def unknownTypefallBack(tp: Type): base.TypeRep = {
              val tsym = tp.typeSymbol.asType
              if (tsym.isParameter) {
                debug(s"P ${tsym.fullName} ${tsym.owner.isType}")
                assert(tsym.typeParams.isEmpty)
                Base.staticTypeApp(
                  tparams.find(_._1.name.toString === tsym.name.toString).get._2, Nil) // FIXME hygiene
              } else super.unknownTypefallBack(tp)
            }
            // Special handling of references to the method's parameters, and `this` references:
            override def unknownFeatureFallback(x: Tree, parent: Tree) = x match {
              case Ident(TermName(name)) =>
                assert(name === x.symbol.name.toString)
                vparams.iterator.flatten.find(
                  _._1.name.toString === name // FIXME hygiene
                ).get._2 |> Base.readVal
              case This(tpnme) =>
                // TODO handle refs to outer clases: use Map[TypeName,Tree] for self refs
                //assert(tpnme === typeNames.EMPTY || tpnme === templ.symbol.name.toTypeName, (tpnme, templ.symbol.name))
                // ^ weirdly fails, with things like  (MyClass3,<local MyClass3>)
                self
              case _ =>
                super.unknownFeatureFallback(x, parent)
            }
          }
          val expTyp = md.symbol.asMethod.returnType
          assert(md.symbol.typeSignature.finalResultType =:= expTyp, s"${md.tpe.finalResultType} =:= ${expTyp}")
          val res = ME.apply(md.rhs, Some(expTyp))
          val sym = ME.getMtd(md.symbol.asMethod)
          q"..${
            ME.vparams.flatMap(_.map(vp => vp._2.toValDef))
          }; new Method[Any,Scp]($sym,${
            ME.tparams.map(tp => tp._2._2)
          },${
            ME.vparams.map(_.map(tv => q"$td.Variable.mk(${tv._2.tree},${tv._2.typRep})"))
          },$td.Code($res))($td.CodeType(${ME.liftType(md.rhs.tpe)}))"
      }
      object ME extends MEBase
      
      val fields = templ.body.collect {
        //case vd: ValDef
        //  //if vd.symbol.asTerm.isParameter
        //  if vd.symbol.asTerm.isParamAccessor
        //=>
        //  ???
        case vd: ValDef //if vd.symbol.asTerm.isVar
          //if !vd.symbol.isPrivateThis // this happens for non-var/val parameters, or if the user specified it so
          //|| { if (vd.symbol.asTerm.isVar || vd.symbol.asTerm.isVal)
          //  c.warning(vd.pos, s"Cannot lift a private[this] field."); false }
          //if sign.member(vd.symbol.name).typeSignature.isInstanceOf[NullaryMethodTypeApi]
          if {
            val nmeStr = vd.name.toString
            val nme = TermName(if (nmeStr.endsWith(" ")) nmeStr.init else nmeStr)
            sign.member(nme).typeSignature.isInstanceOf[NullaryMethodTypeApi]
          }
        =>
          val sym = vd.symbol.asTerm
          debug(s"====== Lifting ${sym} ======")
          assert(sym.isVar || sym.isVal, sym)
          debug(sym.isAccessor)
          
          //println(vd.symbol, vd.symbol.isParameter, vd.symbol.asTerm.isParamAccessor)
          
          //assert(vd.name.toString.endsWith(" "), vd) // we're looking at a transformed private[this] field
          //val nme = TermName(vd.name.toString.init)
          // ^ Seems to work consistently in 2.12, but in 2.11 the compiler SOMETIMES does NOT do the renaming!
          val nmeStr = vd.name.toString
          val nme = TermName(if (nmeStr.endsWith(" ")) nmeStr.init else nmeStr)
          
          val self = name match {
            case name: TermName => q"${Ident(name)}"
            //case name: TypeName => q"${Ident(name)}.this" // not type-checked within the scope of the class!
            case name: TypeName => q"(??? : ${Ident(name)})"
          }
          //assert(sym.isVar || sym.isVal)
          //println(sym.isParamAccessor, sym.isGetter, sym.isMethod, sym.isParameter, sym.isPrivateThis, sym.isPrivate)
          //val get = if (sym.isPrivateThis) None else Some {
          //  c.typecheck(q"$self.${nme}").symbol.asMethod alsoApply (get =>
          //    assert(get.asTerm.isGetter, get))
          //}
          //debug(sign.member(vd.symbol.name).typeSignature.isInstanceOf[NullaryMethodTypeApi])
          debug(sign.member(nme).typeSignature |>? {
            //case _: MethodType =>
            case _: NullaryMethodType =>
          })
          //debug(sign.member(vd.symbol.name).typeSignature.isInstanceOf[NullaryMethodType])
          //debug(sign.member(nme).isPrivate)
          //debug(sign.member(nme).isPrivateThis)
          //debug(sign.member(nme).isSynthetic)
          //debug(sign.member(nme).alternatives)
          //debug(sign.member(nme).asTerm.isAccessor)
          val get = c.typecheck(q"$self.${nme}").symbol.asMethod
          assert(get.asTerm.isGetter, get)
          val set = if (sym.isVar) Some {
            c.typecheck(q"$self.${nme} = ???").symbol.asMethod alsoApply (set =>
              assert(set.asTerm.isSetter, set))
          } else None
          
          q"mkField(${vd.name.toString},${ME.getMtd(get)},${set.map(ME.getMtd)},${
            if (vd.rhs.isEmpty) {
              assert(sym.isParamAccessor)
              None
            } else {
              assert(!sym.isParamAccessor)
              debug(s"RHS ${vd.rhs}")
              Some(ME(vd.rhs, Some(sym.typeSignature)))
            }
          })(${ME.liftType(vd.symbol.typeSignature)})"
          
          /*
<<<<<<< HEAD
          q"mkField(${vd.name.toString},${ME.getMtd(get)},Some(${ME.getMtd(set)}),${
            ME(vd.rhs, Some(vd.symbol.typeSignature))
          })(${ME.liftType(vd.symbol.typeSignature)})"
=======
          //q"mkField(${nme.toString},${get.map(ME.getMtd)},${set.map(ME.getMtd)},${
          q"mkField(${nme.toString},${ME.getMtd(get)},${set.map(ME.getMtd)},${
            if (vd.rhs.isEmpty) {
              assert(sym.isParamAccessor)
              None
            } else {
              assert(!sym.isParamAccessor)
              debug(s"RHS ${vd.rhs}")
              Some(ME(vd.rhs, Some(sym.typeSignature)))
            }
          })(${ME.liftType(sym.typeSignature)})"
>>>>>>> WIP
          */
      }
      (fields, methods)
    }
    
    val objSelf = q"this"
    
    val trees = tcls match {
      case None =>
        val (fields, methods) = liftTemplate(tobj.name, tobj.impl, objSelf, tobj.symbol.typeSignature)
        q"""
        new $d.TopLevel.Object[${tobj.name}.type](${tobj.name.toString})($d.Predef.implicitType[${tobj.name}.type])
        with $d.TopLevel.ObjectWithoutClass[${tobj.name}.type] {
          val parents = Nil
          val fields: List[AnyField] = $fields
          val methods: List[AnyMethod[Scp]] = $methods
        }
        """
      case Some(tcls) =>
        val (fields, methods) = liftTemplate(tobj.name, tobj.impl, objSelf, tobj.symbol.typeSignature)
        val cls2 = tcls
        val clsSelf = q"self.rep"
        val (cfields, cmethods) = liftTemplate(cls2.name, cls2.impl, clsSelf, tcls.symbol.typeSignature)
        q"""
        object obj extends $d.TopLevel.Object[${tobj.name}.type](${tobj.name.toString})($d.Predef.implicitType[${tobj.name}.type])
                   with $d.TopLevel.ObjectWithClass[${tobj.name}.type] {
          val parents = Nil
          val fields: List[AnyField] = $fields
          val methods: List[AnyMethod[Scp]] = $methods
          lazy val companion = Some(cls) // lazy otherwise diverges!
        }
        object cls extends $d.TopLevel.Clasz[${tcls.name}](${tcls.name.toString},Nil)($d.Predef.implicitType[${tcls.name}])
                   with $d.TopLevel.ClassWithObject[${tcls.name}] {
          val parents = Nil
          val self = $d.Variable[${tcls.name}]("this")($d.Predef.implicitType[${tcls.name}])
          val fields: List[AnyField] = $cfields
          val methods: List[AnyMethod[Scp]] = $cmethods
          val companion = Some(obj)
        }
        cls
        """
        // ^ FIXME Variable[${tcls.name}] won't work with generic classes
    }
    
    val res = q"""
      ..${Base.mkSymbolDefs}
      $trees
    """
    
    debug(s"====== Generated ====== ${showCode(res)}")
    //debug(s"Symbols: ${Base.symbols}")
    res
  }
  
}
