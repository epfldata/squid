package squid
package feature

import utils.Debug._

import squid.utils.meta.{RuntimeUniverseHelpers => ruh}
import ruh.{sru, srum}

class Base {
  def foo = 42
  class Test[A] {
    def bar = 666
  }
  object Test { def apply[T] = new Test[T] }
  class TestObject
  object TestObject
}
object Derived extends Base {
  class TestDerived extends Test[Int]
  object TestDerived { def apply() = new TestDerived() }
  def apply() = new Derived
}
class Derived {
  def foo = 0.5
}

class InheritedDefs extends MyFunSuite {
  import TestDSL.Predef._
  
  test("Inherited Methods") {
    
    val d = code"Derived"
    
    assert(d.trep.tpe =:= typeRepOf[Derived.type].tpe)
    assert(d.trep.tpe =:= sru.typeOf[Derived.type])
    
    eqt(d.trep, typeRepOf[Derived.type])
    same(code"Derived.foo".run, 42)
    same(code"$d.foo".run, 42)
    
    same(code"(new Derived()).foo".run, 0.5)
    same(code"(Derived()).foo".run, 0.5)
    
    same(TestDSL.loadMtdSymbol(TestDSL.loadTypSymbol("squid.feature.Derived"), "foo", None), sru.typeOf[Derived].member(sru.TermName("foo")))
  }
  
  test("Inherited Classes") {
    
    val ndti = code"new Derived.Test[Int]"
    val ndtd = code"new Derived.TestDerived"
    eqt(ndti.trep, code"Derived.Test[Int]".trep)
    eqt(ndtd.trep, code"Derived.TestDerived()".trep)
    
    eqt(ndti.trep, new base.TypeRep(sru.typeOf[Derived.Test[Int]]))
    assert(ndti.trep =:= new base.TypeRep(sru.typeOf[Derived.Test[Int]]))
    assert(!(ndtd.trep =:= new base.TypeRep(sru.typeOf[Derived.Test[Int]])))
    assert(ndtd.trep <:< new base.TypeRep(sru.typeOf[Derived.Test[Int]]))
    
    same(code"$ndtd.bar".run, 666)
    
    
    val manual_ndtd = {
      import TestDSL._
      val dtp = TypeRep(sru.typeOf[Derived.TestDerived])
      methodApp(newObject(dtp),
        loadMtdSymbol(loadTypSymbol(ruh.encodedTypeSymbol(sru.typeOf[Derived.TestDerived].typeSymbol.asType)), "<init>", None), Nil, Args()::Nil, dtp)
    }
    eqt(ndtd.rep, manual_ndtd)
    
  }
  
  test("Inherited Objects") { // FIXME
    
    //val to = dbgir"Derived.TestObject"
    //eqt(to.trep, typeRepOf[Derived.TestObject.type])
    
    /*
    // works
    val TestObject$macro$12 = SimpleTypeRep(sru.typeOf[Derived.TestObject.type])
    val q = Quoted[scp.feature.Derived.TestObject.type, Any](
      TestDSL.moduleObject("_root_.scp.feature.Derived.TestObject", TestObject$macro$12))
    println(q.run)
    */
    
    /*
    println(TestDSL.DynamicTypeRep.apply("scp.feature.Derived"))
    println(TestDSL.DynamicTypeRep.apply("scp.feature.Derived").typ =:= sru.typeOf[Derived.type])
    
    println(TestDSL.DynamicTypeRep.apply("scp.feature.Derived.TestObject"))
    */
  }
  
  
}





