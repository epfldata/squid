package stagerwr
package compiler

import Embedding.Predef._
import Embedding.Quasicodes._
import java.io.File
import java.io.PrintStream

import example.VarNormalizer
import squid.utils._
import squid.ir._
import squid.lang._
import squid.anf.analysis
import squid.anf.transfo
import Embedding.Rep
import Embedding.{Block, AsBlock, WithResult, GeneralClosure, Lambda}
//import Embedding.{Block, AsBlock, WithResult, GeneralClosure, ConstantShape}

/*

TODO HL rewritings to open opportunities for flatmap fusion


see also comments in sfusion2!

The gist of the idea:
we normalize/order all operations so that:
 - flatten or filter followed by drop/take is at the end of any nested thingy
 - we merge map on flatten into the left of the flatten
 - drop/take are as far at the beginning as possible
 - put drop at the left of take
 - take/drop are extracted from zipWith args

*/

/**
  * Created by lptk on 13/06/17.
  */
class Compiler extends Optimizer {
  
  val base: Embedding.type = Embedding
  
  
  def pipeline = (r: Rep) => {
    //val r0 = Embedding.debugFor (ImplFlowOptimizer pipeline r)
    val r0 = ImplFlowOptimizer pipeline r
    println("--- ImplFlowOptimizer ---\n"+r0)
    
    val r1 = ImplLowering pipeline r0
    println("--- ImplLowering ---\n"+r1)
    //r1
    
    val r2 = FlatMapFusion pipeline r1
    println("--- FlatMapFusion ---\n"+r2)
    //r2
    
    // ---
    
    ////val r1 = ImplFold pipeline r0
    //val r1 = ImplFold pipeline (FoldInlining pipeline r0)
    //println("--- ImplFold ---\n"+r1)
    
    //val r2 = ImplLowering pipeline r1
    ////val r2 = r1
    //println("--- ImplLowering ---\n"+r2)
    //r2
    
    //val r3 = CtorInline pipeline r1
    //r3
    
    //val r3 = LowLevelNorm pipeline (VarFlattening pipeline r2) // FIXME probably crashes because pattern norm is on
    //val r3 = LowLevelNorm pipeline (/*VarFlattening pipeline*/ r2)
    val r3 = VarFlattening pipeline r2
    println("--- Low Level ---\n"+r3)
    r3
    
    //val r3 = Flow pipeline r2
    //println("--- Logic Flow ---\n"+r3)
    //r3
    
  }
  
}




import Strm._
import Embedding.Predef._


object ImplFlowOptimizer extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer with FixPointTransformer { self =>
//object ImplFlowOptimizer extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer with FixPointTransformer { self =>
  
  rewrite {
      
    case code"($as: Strm[$ta]).map[$tb]($f).take($n)" =>
      //println(0)
      code"$as.take($n).map[$tb]($f)"
      
    //case ir"($as: Strm[$ta]).map[$tb]($f).drop($n)" =>
    //  ir"$as.drop($n).map[$tb]($f)"
      
    case code"($as: Strm[$ta]).take($n).take($m)" =>
      code"$as.take($n max $m)"
      
    //case ir"($as: Strm[$ta]).take($n).drop($m)" =>
    //  ir"$as.drop($m).take($n - $m)" // FIXME careful with drop(-n) ... normally valid
    //  
    //case ir"($as: Strm[$ta]).drop($n).drop($m)" =>
    //  ir"$as.drop($n + $m)"
      
      
    case code"($as: Strm[$ta]).map[$tb]($fb).map[$tc]($fc)" =>
      code"$as.map($fb andThen $fc)"
      
    case code"($as: Strm[$ta]).flatMap[$tb]($fb).map[$tc]($fc)" =>
      //ir"$as.flatMap(_.map(_.map($fb andThen $fc))"
      code"$as.flatMap(as => $fb(as).map($fc))"
      
    case code"($as: Strm[$ta]).map[$tb]($fb).flatMap[$tc]($fc)" =>
      code"$as.flatMap($fb andThen $fc)"
      
    // TODO?
    //case ir"($as: Strm[$ta]).filter($pred)" =>
    //  ir"$as.flatMap(a => singleIf(a,$pred(a)))"
      
      
      
      
      
    // (old) Assumption: uninlined streams have simple implem -- a producer which implem can be used efficiently, eg. Strm.range 
    //  TODO filter?
      
    // Folding
      
    case code"($as: Strm[$ta]).foreach($f)" =>
      code"consumeWhile($as){a => $f(a); true}"
      
    case code"consumeWhile(($as: Strm[$ta]).map[$tb]($f))($g)" =>
      code"consumeWhile($as)($f andThen $g)"
    
    case code"consumeWhile(($as: Strm[$ta]).take($n))($f)" =>
      //ir"var taken = 0; consumeWhile($as){a => taken < $n && $f(a) }"
      code"var taken = 0; consumeWhile($as){a => val t = taken; taken = t+1; t < $n && $f(a) }"
    
    case code"consumeWhile(($as: Strm[$ta]).flatMap[$tb]($f))($g)" =>
      //ir"consumeWhileNested($as)($f andThen $g)"
      code"consumeWhileNested($as)($f)($g)"
      
      
    // Zipping
      
    case code"consumeWhile(($as:Strm[$ta]).zipWith[$tb,$tc]($bs)($f))($g)" =>
      
      val as0 = code"(k:$ta=>Bool) => consumeWhile($as)(k)" transformWith ImplFlowOptimizer
      val bs0 = bs transformWith ImplFlowOptimizer
      
      println(as0)
      println(bs0)
      
      ???
    
    
    
  }
  
}





/*
object NeatClosure {
  def unapply[T:IRType,C](x: IR[T,C]): Some[NeatClosure[T,C]] = x match {
    case ir"val x: $xt = $init; $body: T" =>
      val bodyFun = (x: IR[xt.Typ,C]) => body subs 'x -> x
      ////val Some(clos) = unapply(body)
      //Some(new NeatClosure[T,C] {
      //  
      //})
      
      ir"var x: $xt = $init; ${bodyFun andThen { b =>
        unapply(b).get.term
      }}(xt)"
      
      ???
    case _ => Some(new NeatClosure[T,C] {
      type C0 = C
      type Env = Unit
      val term = x
      val reinit = (_:Env) => ir"()"
      def make[R](code: (Env => IR[R,C])): IR[R,C] = code(())
    })
  }
}
abstract class NeatClosure[T,C] {
  type C0 <: C
  type Env
  val term: IR[T,C0]
  //val term: Env => IR[T,C0]
  val reinit: Env => IR[Unit,C0]
  def make[R](code: (Env => IR[R,C0])): IR[R,C]
  override def toString: String = s"NeatClosure($term)"
}
*/





// TODO use custom xtors like Nested(_) instead of flatten(_); should match flatten(_), flatten(_).drop, etc.
//object ImplFold extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer with FixPointTransformer { self =>
object FlatMapFusion extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer with FixPointTransformer { self =>
  
  rewrite {
    
    //case ir"($as: Strm[$ta]).flatMap[$tb]($f)" =>
    //  ???
    
    //case ir"flatten[$ta]((k:Producer[ta]=>Unit) => $body:ta)" =>
    //case ir"flatten[$ta]((k:Consumer[Producer[ta]]) => $body:ta)" =>
    //case ir"flatten[$ta]((k:Consumer[Producer[ta]]) => $body:Producer[ta])" =>
    // ^ nope, all wrong -- type check because of stupid Unit coercion
    case code"flatten[$ta]((k:Consumer[Producer[ta]]) => $body:Unit)" =>
      println(body)
      ???
      
    //case ir"flatten($ass: Producer[Producer[$ta]])" =>
    //  //ass match {
    //  //  case ir"(k:Producer[$ta]=>Unit) => $body" =>
    //  //    println("B "+body)
    //  //}
    //  ???
      
    //case ir"doFlatMap[$ta,$tb]($p,$f)" =>
    case code"doFlatMap[$ta,$tb]($p, a => ${NeatClosure(clos)})" =>
      //println(clos)
      //val res = clos.make[Nothing] { (term,reset) =>
      //  println(term,reset)
      //  ir"$reset(); if (readInt>0) $reset(); ???"
      //}
      //println(res)
      //readInt
      
      //val res = clos.make { (term,reset) =>
      //  println("TR: ",term,reset)
      //  term match {
      //    case ir"(k:Consumer[$$tb]) => $body: Unit" =>
      //      //???
      //      ir"()"
      //  }
      //}
      //println(res)
      //res
      //???
      
      fuseFlatMap(p, clos)
      //fuseFlatMap[ta.Typ,tb.Typ](p, clos)
      
    case code"doFlatMap[$ta,$tb]($p, ${Lambda(body)})" =>   // goal is to extract lambda without making holes
      //fuseFlatMap(p, clos)
      ???
    
      
      //ir"val p = $p; (k:Consumer[$tb]) => {  }"
      
      //???
    
  }
  
  //def fuseFlatMap[A:IRType,B:IRType,C](p: IR[Producer[A],C], clos: NeatClosure[Producer[B],C{val a:A}]) = {
  //def fuseFlatMap[A:IRType,B:IRType,C](p: IR[Producer[A],C], clos: NeatClosure[Producer[B],C{val a:A}]): IR[Producer[B],C] = {
  def fuseFlatMap[A:CodeType,B:CodeType,C](p: Code[Producer[A],C], clos: NeatClosure[Producer[B],C{val a:A}]): Code[Producer[B],Any] = { // ^ FIXME why?? :-(
    val res = clos.make { (term,reset) =>
    //val res = clos.make[Producer[B]] { (term,reset) =>
      println("TR: ",term,reset)
      //println("TR: ",term,reset.rep.dfn)
      /*
      term match {
        //case ir"(k:Consumer[$$tb]) => $body: Unit" =>
        case ir"(k:Consumer[T]) => $body: Unit" =>
          //???
          ir"""
            var curA: Option[A] = None
            (k:Consumer[T]) => {
              
            }
          """
      }
      */
      //ir"""
      //  var curA: Option[A] = None
      //  (k:Consumer[T]) => {
      //    var consumed = false
      //    var didReset = false
      //    while(!consumed && !didReset) {
      //      $term { b =>
      //        consumed = true
      //        didReset = false
      //      }
      //      if (!consumed) {
      //        didReset = true
      //        
      //      }
      //    }
      //  }
      //"""
      // TODO need to make sure that `term` is a lambda, otherwise unsound
      //Embedding.SimplePredef unsound
      //
      ///*
      code"""
        var curA: Option[A] = None
        (k:Consumer[B]) => {
          var consumed = false
          loopWhile {
            if (!curA.isDefined) $p{a => curA = Some(a); $reset() }
            curA.fold(false) { a =>
              $term { b =>
                k(b)
                consumed = true
              }
              if (!consumed) { curA = None; true } else false
            }
          }
        }
      """
      //*/
      /*
      ir"""
        var curA: Option[A] = None
        (k:Consumer[B]) => {
          println("curA = "+curA)
          var consumed = false
          loopWhile {
            if (!curA.isDefined) $p{a => curA = Some(a); println("RESET"); $reset() }
            println("curA' = "+curA)
            curA.fold(false) { a =>
              $term { b =>
                k(b)
                consumed = true
              }
              if (!consumed) { curA = None; true } else false
            }
          }
        }
      """
      */
    }
    println(res)
    //println(res.rep.dfn)
    Embedding.SimplePredef unsound
    res
    // subs 'a -> {
    //  println("?????????????????")
    //  Abort()
    //}
  }

}


//object FoldInlining extends Embedding.Lowering('Fold) with TopDownTransformer //with FixPointTransformer
object FlatMapInlining extends Embedding.Lowering('FlatMap) with TopDownTransformer //with FixPointTransformer

//object ImplLowering extends Embedding.Lowering('Impl) with TopDownTransformer
object ImplInlining extends Embedding.Lowering('Impl)
object ImplCtorInline extends Embedding.SelfCodeTransformer with CodeTransformer with FixPointTransformer {
  def transform[T,C](code: Code[T,C]): Code[T,C] = (code match {
    case code"(if ($c) $thn else $els : Strm[$ta]).producer" => code"if ($c) $thn.producer else $els.producer"
    case code"Strm($pf).producer" => pf
    case code"val $st = Strm[$t]($pf); $body: $bt" =>
      body rewrite { case code"$$st.producer" => pf } subs 'st -> {System.err.println("huh s");return code}
    case _ => code
  }).asInstanceOf[Code[T,C]]
}
object ImplLowering extends Embedding.TransformerWrapper(ImplInlining, ImplCtorInline) with TopDownTransformer with FixPointTransformer
//object ImplLowering extends Embedding.TransformerWrapper(ImplInlining, ImplCtorInline) with BottomUpTransformer with FixPointTransformer


object VarFlattening extends Embedding.SelfTransformer with transfo.VarFlattening with TopDownTransformer

/*
//val LowLevelNorm extends Embedding.SelfTransformer with LogicNormalizer with transfo.VarInliner with FixPointRuleBasedTransformer with BottomUpTransformer
// ^ Some optimizations are missed even in fixedPoint and bottomUp order, if we don't make several passes:
object LowLevelNorm extends Embedding.TransformerWrapper(
  // TODO var simplification here,
  new Embedding.SelfTransformer 
    //with transfo.LogicNormalizer // already online in Embedding! 
    with FixPointRuleBasedTransformer 
    with BottomUpTransformer { rewrite {
      case ir"squid.lib.uncheckedNullValue[$t]" => nullValue[t.Typ]
    }}
) with FixPointTransformer
*/

object Flow extends Embedding.SelfTransformer with transfo.LogicFlowNormalizer


