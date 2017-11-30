package stagerwr
package compiler

/**
  * Created by lptk on 22/06/17.
  */
//class NeatClosure {
//}

import squid.lib.{Var,uncheckedNullValue}
//import Embedding.Predef._
import Embedding.Predef.{Code=>IR,_}
import Embedding.SimplePredef.{Rep=>Code,_}

object NeatClosure {
  
  def mkFun[S,T](body: IR[T,{val x:S}]) = (x: Code[S]) => body subs 'x -> x.unsafe_asClosedCode
  
  //def rec[T:CodeType](t: Code[T], reset: Code[() => Unit]): Code[T] = {
  def rec[T:CodeType,R:CodeType](t: Code[T], reset: Code[() => Unit], term_reset: (Code[T], Code[() => Unit]) => Code[R]): Code[R] = {
  //def rec[T:CodeType,R:CodeType,C](t: Code[T], reset: Code[() => Unit], term_reset: (Code[T], Code[() => Unit]) => IR[R,C]): IR[R,C] = {
    println(s"REC $t $reset")
    t match {
      //def rec[T:CodeType](t: Code[T], reset: Code[Unit => Unit]): NeatClosure[T,Any] = t match {
    
      case code"val x = Var[$xt]($init); $body: T" =>
      
        val bodyFun = mkFun(body)
        //println("BODY "+body)
        //println("BODY' "+bodyFun(ir"???"))
        
        //ir"val x = Var($init); ${(x:Code[Var[xt.Typ]]) =>
        //ir"val x = Var[$xt](uncheckedNullValue); ${(x:Code[Var[xt.Typ]]) =>
        code"val mut_env = Var(uncheckedNullValue[$xt]); ${(x:Code[Var[xt.Typ]]) =>
          //val b = bodyFun(ir"$x")
          val b = bodyFun(x)
          rec(b, code"() => { $reset(); $x := $init }", term_reset)
        }(mut_env)"
        
        
      case code"val x: $xt = $init; $body: T" =>
      
        val bodyFun = mkFun(body)
        //val bodyFun = (x: IR[xt.Typ,C]) => body subs 'x -> x
      
        //ir"var x: $xt = $init; ${bodyFun andThen { b =>
        //  //unapply(b).get.term
        //  rec(b,reset)
        //}}(x)"
        //ir"val x = Var($init); ${(x:Code[Var[xt.Typ]]) =>
        //ir"val x = Var[$xt](uncheckedNullValue); ${(x:Code[Var[xt.Typ]]) =>
        code"val env = Var(uncheckedNullValue[$xt]); ${ (x:Code[Var[xt.Typ]]) =>
          ///*
          val b = bodyFun(code"$x.!")  // UNSAFE: the var access is let-bound, and rec ends up in an infinite loop!
          rec(b, code"() => { $reset(); $x := $init }", term_reset)
          //*/
          /*
          // Does not work: `acc` ends up being bound in the context, and is thus not up to date
          ir"val acc = $x.!; ${ (a:Code[xt.Typ]) =>
            val b = bodyFun(a)
            rec(b, ir"() => { $reset(); $x := $init }", term_reset)
          }(acc)"
          */
          ???
        }(env)"
        
      //???
        
    
      case _ =>
        //println(reset)
        //???
        //new NeatClosure[T,Any] {
        //}
        term_reset(t,reset)
        
      //case _ => Some(new NeatClosure[T,C] {
      //  type C0 = C
      //  type Env = Unit
      //  val term = x
      //  val reinit = (_:Env) => ir"()"
      //  def make[R](code: (Env => IR[R,C])): IR[R,C] = code(())
      //})
    }
  }
  def unapply[T:CodeType,C](x: IR[T,C]): Some[NeatClosure[T,C]] = {
    //Some(rec(x, ir"() => ()"))
    //???
    Some(new NeatClosure[T,C] {
      //def make[R:CodeType](term_reset: (Code[T], Code[() => Unit]) => Code[R]): Code[R] = rec(x, ir"() => ()", term_reset)
      //def make[R:CodeType,C](term_reset: (Code[T], Code[() => Unit]) => IR[R,C]): IR[R,C] = 
      //  rec(x, ir"() => ()", term_reset.asInstanceOf[(Code[T], Code[() => Unit]) => Code[R]]).asInstanceOf[IR[R,C]]
      def make[R:CodeType,D](term_reset: (IR[T,C], IR[() => Unit,C]) => IR[R,D]): IR[R,D] = 
        rec(x, code"() => ()", term_reset.asInstanceOf[(Code[T], Code[() => Unit]) => Code[R]]).asInstanceOf[IR[R,D]]
    })
  }
}
//abstract class NeatClosure[T,C] {
//  //type C0 <: C
//  //type Env
//  //val term: IR[T,C0]
//  ////val term: Env => IR[T,C0]
//  //val reinit: Env => IR[Unit,C0]
//  //def make[R](code: (Env => IR[R,C0])): IR[R,C]
//  //override def toString: String = s"NeatClosure($term)"
//}
//case class NeatClosure[T,C]()
//type NeatClosure[T,C] = ((Code[T],Code[() => Unit]) => Code[T]) => Code[T]
abstract class NeatClosure[T,C] {
  //def make[R](term: Code[T], reset: Code[() => Unit])
  //def make[R](term_reset: (Code[T], Code[() => Unit]) => R): R
  //def make[R:CodeType](term_reset: (Code[T], Code[() => Unit]) => Code[R]): Code[R]
  //def make[R:CodeType,C](term_reset: (Code[T], Code[() => Unit]) => IR[R,C]): IR[R,C]
  def make[R:CodeType,D](term_reset: (IR[T,C], IR[() => Unit,C]) => IR[R,D]): IR[R,D]
}


