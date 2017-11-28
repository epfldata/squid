package squid
package anf

import utils._
import ir._
import squid.lib.{transparent, transparencyPropagating}

/**
  * Created by lptk on 22/02/17.
  */
class EffectSystemTests extends MyFunSuite(SimpleANFTests.DSLWithEffects) {
  import DSL.Predef._
  import EffectSystemTests._
  import SimpleEffect._
  
  def stmts(q: Code[Any,Nothing]) = q.rep.asBlock._1
  def stmtsNumIs(n: Int)(q: Code[Any,Nothing]) = assert(stmts(q).size == n)
  
  test("Basics") {
    
    assert(code"42".rep.effect == Pure)
    assert(code"42.toDouble".rep.effect == Pure)
    assert(code"println".rep.effect == Impure)
    
    assert(code"val n = 42; val m = n+1; println(m); 'ok".rep.asBlock._1.size == 1)
    
    code"true && {identity(42.toDouble);true} && false" eqt code"(true:Bool) && true && false"
    eqt(code"true && {println;true} && false".rep.asBlock._1.head.fold(_._2,identity), code"true && {println;true}".rep)
    
    assert(code"IndexedSeq().size + Nil.size + Seq().size".rep.asBlock._1.size == 5) // used to be 3 because GenericCompanion.apply was handled wrongly
    // ^ currently, `.size` on immutable collections is not viewed as pure; this is more tricky because `size` is defined
    // in a generic class, and so should only be pure if the receiver is an immutable collection... not expressible withb current infra
    // very similarly, we now have Seq.apply and IndexedSeq.apply not pure because they're from GenericCompanion, 
    // the same as for mutable.Seq.apply (which is obviously stateful)
    
  }
  
  test("Lambdas") {
    
    assert(code"(x:Any) => println".rep.effect == Latent)
    assert(code"(() => println):(() => Any)".rep.effect == Latent)
    
    assert(code"applyOnce0(() => println)".rep.effect == Impure)
    assert(code"applyOnce1((x:Any) => println)".rep.effect == Impure)
    assert(code"applyTwice0(() => () => println)".rep.effect == Impure)
    assert(code"applyTwice1((x:Any) => (y:Any) => println)".rep.effect == Impure)
    
    assert(code"(x:Any) => (x:Any) => println".rep.effect == Latent)
    assert(code"((x:Any) => (x:Any) => println)(1)".rep.effect == Latent) // that happens because this is a let-binding!! (otherwise, should be `Impure`)
    assert(code"((x:Any) => (x:Any) => println)(1)(2)".rep.effect == Impure)
    
    assert(code"() => println".rep.effect == Latent)
    assert(code"() => () => println".rep.effect == Latent)
    assert(code"(() => () => println)()".rep.effect == Impure)
    assert(code"(() => () => println)()()".rep.effect == Impure)
    
    // thanks to an add-hoc entry for `identity` in `transparencyPropagatingMtds`:
    assert(code"identity((x:Int)=>print(x))".rep.effect == Latent)
    assert(code"identity((x:Int)=>x)".rep.effect == Pure)
    
  }
  
  test("Options") {
    
    assert(code"Some(Some(42)).get.get".rep.asBlock._1.isEmpty)
    
    assert(code"val a = Option; a.empty[Int]".rep.asBlock._1.isEmpty)
    
    assert(code"Right(true)".rep.asBlock._1.isEmpty)
    // ^ both `scala.`package`.Right` and `scala.`package`.Right.apply(true)` successfully viewed as trivial by ANF
    
    // `???` scheduled before `s.map`, which makes transfos not straightforward! cf. RewritingTests
    code"var s: Option[Int] = None; s.map[Int](???)" eqt code"""{
      var s_0: scala.Option[scala.Int] = scala.None;
      val x_1 = s_0;
      val x_2 = ((scala.Predef.???): Nothing);
      x_1.map[scala.Int](x_2)
    }"""
    
    // Those are effectful and should not be elided!
    assert(code"Some(42).map(a => println(a)); ()".rep.asBlock._1.size == 1)
    assert(code"Some(()).getOrElse(println); 42".rep.asBlock._1.size == 1)
    
  }
  
  test("Tuples") {
    
    code"(1,2).swap._1" |> stmtsNumIs(0)
    code"(1,(x:Int)=>print(x)).swap._1" |> stmtsNumIs(0)
    code"(1,(x:Int)=>print(x)).copy(_1 = readInt)._1" |> stmtsNumIs(1)
    
  }
  
  test("From Annotations") {
    
    code"foo + foo" |> stmtsNumIs(0)
    code"myId((x:Int) => x+foo)" |> stmtsNumIs(0)
    code"myId((x:Int) => x+foo)(foo)" |> stmtsNumIs(0)
    code"myId((x:Int) => x+foo)(readInt)" |> stmtsNumIs(1)
    code"myId((x:Int) => {print(x);x})" |> stmtsNumIs(0) // returned expression is impure
    code"myId((x:Int) => {print(x);x}); 42" eqt code"42"   // expr with latent effect is ignored
    code"val mid = myId((x:Int) => {print(x);x}); mid(42)" |> stmtsNumIs(0)
    code"val mid = myId((x:Int) => {print(x);x}); mid(readInt)" |> stmtsNumIs(1)
    
  }
  
  test("Collections") {
    import scala.collection.mutable.Set
    import scala.collection.mutable.Buffer
    
    code"Set(1,2,3).head" |> stmtsNumIs(1)
    code"Buffer(1,2,3)+=1" |> stmtsNumIs(1)
    
    code"List(1,2,3).head" |> stmtsNumIs(0)
    code"println(List.empty[Int])" |> stmtsNumIs(0)
    
  }
  
}
object EffectSystemTests {
  def applyOnce0(f: () => Unit) = f()
  def applyOnce1(f: Any => Unit) = f(())
  def applyTwice0(f: () => () => Unit) = f()()
  def applyTwice1(f: Any => Any => Unit) = f(())(())
  
  @transparent
  def foo = 42
  
  @transparencyPropagating
  def myId(f: Int => Int): Int => Int = f
  
}
