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
import lang._
import meta.RuntimeUniverseHelpers._
import squid.lang.Base
import sru._

import scala.reflect.ClassTag
import scala.reflect.runtime.ScalaReflectSurgeon

/**
  * TODO: a smarter version that creates the invokers and returns a _runner_ that can be ran more efficiently.
  */
class BaseInterpreter extends Base with CrossStageEnabled with RuntimeSymbols with TraceDebug {
  import BaseInterpreter._
  
  type TypSymbol = ScalaTypeSymbol
  
  type Rep = Any
  class BoundVal(var value: Rep = null)
  type TypeRep = () => TypSymbol
  
  
  def repEq(a: Rep, b: Rep): Boolean = a == b
  def typLeq(a: TypeRep, b: TypeRep): Boolean = true
  
  
  def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal = new BoundVal()
  def readVal(v: BoundVal): Rep = v.value
  def const(value: Any): Rep = value
  
  /* Note: HOAS may be nicer to have here, but we can't abstract over arity with HOAS so the rest of the code would suffer anyway */
  def lambda(params: List[BoundVal], body: => Rep): Rep = BaseInterpreterMacros.genLambdaBody
  /* The above macro generates code following the pattern below for all 22 cases:  
    params match {
      case Nil => () => body
      case x0 :: Nil => (p0: Any) => x0.value = p0; body
      case x0 :: x1 :: Nil => (p0: Any, p1: Any) => x0.value = p0; x1.value = p1; body
      // ...
    }
  */
  
  def byName(arg: => Rep): Rep = () => arg
  
  
  def newObject(tp: TypeRep): Rep = New(tp().asClass)
  case class New(cls: ClassSymbol)
  
  def staticModule(fullName: String): Rep = {
    val sym = srum.staticModule(fullName)
    if (sym.isJava) return srum.runtimeClass(sym.companion.asType.asClass)
    
    //println(s"Mod $sym: "+srum.classSymbol(self.getClass))
    //println(s"Mod: "+srum.classSymbol(typeOf[scp.lib.Var.type].typeSymbol.asClass))
    //println(s"Mod: "+srum.classSymbol(classOf[scp.lib.Var.type]))
    
    val mm = srum.reflectModule(sym)
    
    mm.instance
  }
  def module(prefix: Rep, name: String, typ: TypeRep): Rep = prefix.getClass.getMethod(name).invoke(prefix)
  
  /** These pesky primitive types have a tendency to change class symbol and break everything!
    * eg: Int -> scala.Int instead of Int -> int */
  private def watchPrimitives(): Unit = {
    val c = ScalaReflectSurgeon.cache
    c.enter(ByteCls, ByteType.typeSymbol.asClass)
    c.enter(CharCls, CharType.typeSymbol.asClass)
    c.enter(ShortCls, ShortType.typeSymbol.asClass)
    c.enter(IntCls, IntType.typeSymbol.asClass)
    c.enter(LongCls, LongType.typeSymbol.asClass)
    c.enter(FloatCls, FloatType.typeSymbol.asClass)
    c.enter(DoubleCls, DoubleType.typeSymbol.asClass)
    c.enter(BoolCls, BoolType.typeSymbol.asClass)
    c.enter(VoidCls, VoidType.typeSymbol.asClass)
  }
  
  def methodApp(self: Rep, _mtd: MtdSymbol, targs: List[TypeRep], argss: List[ArgList], tp: TypeRep): Rep = {
    
    watchPrimitives()
    
    debug(s"\nSelf: '$self' ${self.getClass}\nMtd: "+_mtd.fullName+" "+_mtd.isJava)
    
    lazy val args = argss flatMap {
      case Args(reps @ _*) => reps
      case ArgsVarargs(Args(reps @ _*), Args(vreps @ _*)) => reps :+ vreps
      case ArgsVarargSpliced(Args(reps @ _*), vrep) => reps :+ vrep
    }
    
    self match {
      case New(cls) =>
        return srum.reflectClass(cls).reflectConstructor(_mtd).apply(args:_*)
      case _ =>
    }
    
    val cls = srum.classSymbol(if (self == null) classOf[Null] else self.getClass)
    if (cls.isJava && cls.isModuleClass) {
      reflect.runtime.ScalaReflectSurgeon.cache.enter(self.getClass, cls.companion.asClass)
    }
    
    debug(s"Cls $cls ${cls.isModuleClass}") // object Var true
    //debug(s"Members ${cls.toType.members.map("\n"+_).mkString}")
    //debug(s"Own ${mtd.owner} ${mtd.owner==cls}")
    
    /** A hack (again): try to retrieve the method from the `cls` symbol of `self`,
      * to avoid some cases where the reflection API complains that {{{_mtd}}} is not a member of `cls` (it tests its base classes)
      * Note: we may not actually find the method this way, eg for bytecode-less methods like those on primitives */
    
    val f1 = _mtd.paramLists.flatten
    val mtdO = cls.toType.member(_mtd.name).alternatives collect {
      case s: MethodSymbol if {
        val f0 = s.paramLists.flatten
        f0.size == f1.size && (f0 zip f1 forall {
          case (ps, pm) => 
            ps.typeSignature.typeSymbol.fullName == pm.typeSignature.typeSymbol.fullName
        }) // && s.returnType.typeSymbol.fullName == _mtd.returnType.typeSymbol.fullName
        /* ^ Scala methods' erasure can differ only by the return type;
         * however, Scala runtime reflection doesn't know how to invoke them so we fail (in default case below) */
      } => s
    } match { case m::Nil => Some(m) case Nil => None
      case ls => throw new RuntimeException("Interpreting overloaded methods that differ only by their return type is not supported")
    }
    //if (mtdO.isDefined) println(s"Found method ${mtdO.get} in $cls") else println(s"Did not find method ${_mtd} in $cls")
    val mtd = mtdO getOrElse _mtd
    
    if (mtd.isJava && mtd.isStatic) {
      assert(mtd.paramLists.size == 1, "Java methods should have exactly one parameter list.")
      
      val params = mtd.paramLists.head.map(_.typeSignature.erasure) map toJavaCls
      debug("Params erasure: "+params)
      
      val javaMtd = self.asInstanceOf[Class[_]].getMethod(mtd.name.toString, params: _*)
      
      val args = argss.head.reps.asInstanceOf[Seq[Object]]
      
      javaMtd.invoke(null, args: _*)
      
    } else if (mtd.fullName=="scala.Any.asInstanceOf") { // scala.ScalaReflectionException: Any.asInstanceOf requires a type argument, it cannot be invoked with mirrors
      
      self
      
    } else if (mtd.fullName=="scala.Any.isInstanceOf") { // scala.ScalaReflectionException: Any.isInstanceOf requires a type argument, it cannot be invoked with mirrors
      
      System.err.println("Dynamic interpreter cannot execute `isInstanceOf` directly -- returning `true` instead.")
      true
      
    } else {
      
      //debug("Initial signature: "+mtd.typeSignature)
      
      val changes = mtd.paramLists.flatten.filter(_.typeSignature.typeSymbol == ByNameParamClass) map { x =>
        x -> (x.typeSignature -> sru.typeOf[() => Any])
      }
      BaseInterpreter.synchronized { try {
        changes foreach { case (s, (_, newTpe)) => ScalaReflectSurgeon.changeType_omgwtfbbq(s, newTpe) }
        //debug("Modified signature: "+mtd.typeSignature)
        
        val tag = (self match {
          case _: Byte => ClassTag.Byte
          case _: Char => ClassTag.Char
          case _: Short => ClassTag.Short
          case _: Int => ClassTag.Int
          case _: Long => ClassTag.Long
          case _: Float => ClassTag.Float
          case _: Double => ClassTag.Double
          case _: Boolean => ClassTag.Boolean
          case _: Unit => ClassTag.Unit
          case null => ClassTag.Null
          case _ => ClassTag(self.getClass)
        }).asInstanceOf[ClassTag[Any]]
        
        val im = srum.reflect(self)(tag)
        val mm = im.reflectMethod(mtd)
        //println(args)
        
        mm(args: _*)  // oh_and debug("Final Sign: "+mtd.typeSignature)
      }
      finally {
        changes foreach { case (s, (oldTpe, _)) => ScalaReflectSurgeon.changeType_omgwtfbbq(s, oldTpe) }
      }}
      
    }
    
    
  }
  
  def crossStage(value: Any, trep: TypeRep): Rep = value
  def extractCrossStage(r: Rep): Option[Any] = None
  
  
  def uninterpretedType[A: sru.TypeTag]: TypeRep = () => sru.typeOf[A].typeSymbol.asType
  def moduleType(fullName: String): TypeRep = () => ???
  def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = () => typ
  def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep = () => typ
  def recordType(fields: List[(String, TypeRep)]): TypeRep = () => ???
  def constType(value: Any, underlying: TypeRep): TypeRep = () => ???
  
  object Const extends ConstAPI {
    def unapply[T: sru.TypeTag](ir: Code[T, _]): Option[T] = ???
  }
  def hole(name: String, typ: TypeRep): Rep = throw new RuntimeException(s"Cannot interpret hole '$name' of ${typ()}")
  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep = ???
  def splicedHole(name: String, typ: TypeRep): Rep = ???
  def substitute(r: => Rep,defs: scala.collection.immutable.Map[String,Rep]): Rep = ???
  def typeHole(name: String): TypeRep = ???
  
  
}
object BaseInterpreter {
  private val ByteType = typeOf[Byte]
  private val ByteCls = classOf[Byte]
  private val CharType = typeOf[Char]
  private val CharCls = classOf[Char]
  private val ShortType = typeOf[Short]
  private val ShortCls = classOf[Short]
  private val IntType = typeOf[Int]
  private val IntCls = classOf[Int]
  private val LongType = typeOf[Long]
  private val LongCls = classOf[Long]
  private val FloatType = typeOf[Float]
  private val FloatCls = classOf[Float]
  private val DoubleType = typeOf[Double]
  private val DoubleCls = classOf[Double]
  private val BoolType = typeOf[Boolean]
  private val BoolCls = classOf[Boolean]
  private val VoidType = typeOf[Unit]
  private val VoidCls = classOf[Unit]
  
  //def toJavaCls(cls: Class[_]) = cls match { // TODO use classTag[T].runtimeClass instead; see JavaMirrors#preciseClass // TODO or use typeToJavaClass
  /** This is mainly to go around Scala's runtimeClass, which is broken as it returns inconsistent/wrong results depending on the state of its cache... */
  def toJavaCls(cls: Type): Class[_] = cls match {
    case ByteType => ByteCls
    case CharType => CharCls
    case ShortType => ShortCls
    case IntType => IntCls
    case LongType => LongCls
    case FloatType => FloatCls
    case DoubleType => DoubleCls
    case BoolType => BoolCls
    case VoidType => VoidCls
    //case cls => cls
    case cls => srum.runtimeClass(cls)
  }
  
}









