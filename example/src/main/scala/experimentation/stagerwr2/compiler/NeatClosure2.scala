package stagerwr2
package compiler


import squid.lib.{Var,uncheckedNullValue}
import Embedding.Predef._
import Embedding.Quasicodes._
import Embedding.$
import Embedding.SimplePredef._

abstract class AdHocPoly[X] { def apply[T](t: AnyCode[T]): AnyCode[X] => AnyCode[T] }

object NeatClosure2 { // FIXME make reopen polymorphic!
  
  def mkFun[S,T](body: Code[T,{val x:S}]) = (x: AnyCode[S]) => body subs 'x -> x.unsafe_asClosedCode
  
  //def close[X:IRType,R,S](f: Code[X] => Code[R])(k: (Code[R], Code[S] => Code[X] => Code[S]) => Code[S]): Code[S] = {
  def close[X:CodeType,R,S](f: AnyCode[X] => AnyCode[R])(k: (AnyCode[R], AdHocPoly[X]) => AnyCode[S]): AnyCode[S] = {
    import base._
    val fv = freshBoundVal(typeRepOf[X])
    val body = f(Code(base.readVal(fv)))
    //k(body, b => x => 
    //  IR(base.inline(fv,b.rep,x.rep)))
    k(body, new AdHocPoly[X] { 
      def apply[T](b:AnyCode[T]) = x => 
        Code(base.inline(fv,b.rep,x.rep))
    })
  }
  
  def doFlatMapStaged[A:CodeType,B:CodeType](p: AnyCode[Producer[A]], f: AnyCode[A] => AnyCode[Producer[B]]): AnyCode[Producer[B]] = {
    
    //close[A,Producer[B],Nothing](f) { (body,reopen) =>
    close[A,Producer[B],Producer[B]](f) { (body,reopen) =>
      def rec(t: AnyCode[Producer[B]], reset: AnyCode[() => Unit]): AnyCode[Producer[B]] = t match {
          
        case code"val x = Var[$xt]($init); $innerBody: Producer[B]" =>
          println("REC var "+init)
          val innerBodyFun = mkFun(innerBody)
          //rec(body)
          close(innerBodyFun) { (ib,reopenIb) =>
            //ir"val y = Var(uncheckedNullValue[$xt]); ${reopenIb(rec(ib))}(y)"
            code"val y = Var(uncheckedNullValue[$xt]); ${(y:AnyCode[Var[xt.Typ]]) => reopenIb(rec(ib,code"() => { $reset(); $y := $init }"))(y)}(y)"
          }
          
        case code"val x: $xt = $init; $innerBody: Producer[B]" =>
          println("REC val "+init)
          val innerBodyFun = mkFun(innerBody)
          close(innerBodyFun) { (ib,reopenIb) =>
            code"val y = Var(uncheckedNullValue[$xt]); ${(y:AnyCode[Var[xt.Typ]]) => reopenIb(rec(ib,code"() => { $reset(); $y := $init }"))(code"$y.!")}(y)"
          }
          
        case code"$effect; $innerBody: Producer[B]" =>
          println("REC eff "+effect)
          rec(innerBody, code"() => { $reset(); $effect; () }")
          
        case code"(k: (B => Unit)) => $innerBody: Unit" =>
          
          val reot = reopen(t)
          
          val reoreset = reopen(reset)
          //val reoreset = reopen(reset.asInstanceOf[Code[Producer[B]]]).asInstanceOf[Code[A] => Code[() => Unit]]
          
          import Strm._
          
          code"""
            var curA: Option[A] = None
            (k:Consumer[B]) => {
              var consumed_fmr = false
              loopWhile {
                if (!curA.isDefined) $p{a => curA = Some(a); ${reoreset}(a)() }
                curA.fold(false) { a =>
                  ${reot}(a) { b =>
                    k(b)
                    consumed_fmr = true
                  }
                  if (!consumed_fmr) { curA = None; true } else false
                }
              }
            }
          """
          //${reopen(innerBodyFun).asInstanceOf[Code[A] => IR[Producer[B],{val k:Consumer[B]}]]}(a) { b =>
          
          //???

        //case _ => // TODO handle non-fusable case 
          
      }
      rec(body, code"() => ()")
      //??? : Code[Nothing]
    }
    
    //???
    
  }
  
  
}

/*
/**
  * Created by lptk on 28/06/17.
  */
object NeatClosure2 { // FIXME make reopen polymorphic!
  
  //def close[X:IRType,R](f: Code[X] => Code[R])(k: (Code[R], Code[R] => Code[X] => Code[R]) => Code[R]): Code[X => R] = {
  //def close[X:IRType,R](f: Code[X] => Code[R])(k: (Code[R], Code[R] => Code[X] => Code[R]) => Code[R]): Code[R] = {
  def close[X:IRType,R,S](f: Code[X] => Code[R])(k: (Code[R], Code[S] => Code[X] => Code[S]) => Code[S]): Code[S] = {
    import base._
    val fv = freshBoundVal(typeRepOf[X])
    val body = f(IR(base.readVal(fv)))
    k(body, b => x => 
      IR(base.inline(fv,b.rep,x.rep)))
  }
  
  def doFlatMapStaged[A:IRType,B:IRType](p: Code[Producer[A]], f: Code[A] => Code[Producer[B]]): Code[Producer[B]] = {
    
    //close[A,Producer[B],Nothing](f) { (body,reopen) =>
    close[A,Producer[B],Producer[B]](f) { (body,reopen) =>
      def rec(t: Code[Producer[B]], reset: Code[() => Unit]): Code[Producer[B]] = t match {
        //case ir"val x: $xt = $init; $innerBody: Producer[B]" => // TODO
        case ir"val x = Var[$xt]($init); $innerBody: Producer[B]" =>
          println("REC "+init)
          val innerBodyFun = mkFun(innerBody)
          //rec(body)
          close(innerBodyFun) { (ib,reopenIb) =>
            //ir"val y = Var(uncheckedNullValue[$xt]); ${reopenIb(rec(ib))}(y)"
            ir"val y = Var(uncheckedNullValue[$xt]); ${(y:Code[Var[xt.Typ]]) => reopenIb(rec(ib,ir"() => { $reset(); $y := $init }"))(y)}(y)"
          }
          /*
        case ir"(k: (B => Unit)) => $innerBody: Unit" =>
          //reopen(innerBody)
          
          //val innerBodyFun = innerBody : Code[Unit]
          val innerBodyFun = innerBody.asInstanceOf[Code[Producer[B]]] // FIXME
          //val innerBodyFun = mkFun(innerBody) // TODO FIXME
          
          import Strm._
          
          //val reoreset = reopen(reset)
          val reoreset = reopen(reset.asInstanceOf[Code[Producer[B]]]).asInstanceOf[Code[A] => Code[() => Unit]]
          
          ir"""
            var curA: Option[A] = None
            (k:Consumer[B]) => {
              var consumed = false
              loopWhile {
                if (!curA.isDefined) $p{a => curA = Some(a); ${reoreset}(a)() }
                curA.fold(false) { a =>
                  ${reopen(innerBodyFun)}(a) { b =>
                    k(b)
                    consumed = true
                  }
                  if (!consumed) { curA = None; true } else false
                }
              }
            }
          """
          //${reopen(innerBodyFun).asInstanceOf[Code[A] => IR[Producer[B],{val k:Consumer[B]}]]}(a) { b =>
          */
        case ir"(k: (B => Unit)) => $innerBody: Unit" =>
          
          val reot = reopen(t)
          
          //val reoreset = reopen(reset)
          val reoreset = reopen(reset.asInstanceOf[Code[Producer[B]]]).asInstanceOf[Code[A] => Code[() => Unit]]
          
          import Strm._
          
          ir"""
            var curA: Option[A] = None
            (k:Consumer[B]) => {
              var consumed = false
              loopWhile {
                if (!curA.isDefined) $p{a => curA = Some(a); ${reoreset}(a)() }
                curA.fold(false) { a =>
                  ${reot}(a) { b =>
                    k(b)
                    consumed = true
                  }
                  if (!consumed) { curA = None; true } else false
                }
              }
            }
          """
          //${reopen(innerBodyFun).asInstanceOf[Code[A] => IR[Producer[B],{val k:Consumer[B]}]]}(a) { b =>
          
          //???
          
      }
      rec(body, ir"() => ()")
      //??? : Code[Nothing]
    }
    
    //???
    
  }
  
  
}
abstract class NeatClosure2[T,C] {
  def make[R:IRType](term_reset: (Code[T], Code[() => Unit]) => Code[R]): Option[Code[R]]
}
*/
