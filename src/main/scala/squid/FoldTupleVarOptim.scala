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

import utils._
import ir._
import utils.Debug.show

import squid.lib.Var

/** Note: a more up-to-date version, FoldTupleVarOptimNew, uses first-class variable symbols to do the variable falttening
  * more elegantly (and more efficiently). */
trait FoldTupleVarOptim extends FixPointRuleBasedTransformer with TopDownTransformer { self =>
  import base.Predef._
  
  // weirdly, this is now needed:
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  
  //rewrite {
  //  case ir"val $vlol = Var($init: Int); $body: $t" =>
  //    //println(body)
  //    //???
  //    //ir"???"
  //    println(body rep)
  //    println(vlol rep)
  //    val newBody = body rewrite {
  //      //case ir"$$vlol" =>
  //      //  ???
  //      //  ir"Var($init)"
  //      case ir"$$vlol.!" => 
  //        //???
  //        init
  //    }
  //    val res = newBody subs 'vlol -> ir"???"
  //    println(res)
  //    res
  //}
  
    
  rewrite {
    
    case code"($ls: List[$ta]).foldLeft[$tb]($init)($f)" =>
      
      code""" var cur = $init
            $ls foreach { x => cur = $f(cur, x) }
            cur """
      
      /* Or the explicitly-virtualized version: */ 
      //ir""" val cur = Var($init)
      //      $ls foreach { x => cur := $f(cur!, x) }
      //      cur! """
      
      
    case code"($ls: List[$t]) foreach ($f: t => Any)" =>
    //case ir"($ls: List[$t]).foreach[$t2]($f)" => // also works
      
      code""" var iter = $ls
            while (iter.nonEmpty)
            { $f(iter.head); iter = iter.tail } """
      
  }
  
  
  def tuple2Components[A:CodeType,B:CodeType,C](ab: Code[(A,B),C]): Option[ Code[A,C]->Code[B,C] ] = ab match {
    case code"($a:A, $b:B)" => Some(a -> b)
    //case dbg_ir"$ab" => // FIXME? purged type of scrutinee forgets type parameters!! -- can we do better?
    case _ => None
  }
  
  rewrite {
    
    //case ir"var $tup: ($ta, $tb) = $init; $body: $t" => // FIXME give right type to tup FV
    
    //case ir"val $tup: Var[($ta, $tb)] = Var($init); $body: $t" => // FIXME: binding `x @ ir...`
    
    case code"val tup = Var($init: ($ta, $tb)); $body: $t" =>
      
      val a = code"?a: Var[$ta]"
      val b = code"?b: Var[$tb]"
      
      val tup = code"?tup: Var[($ta,$tb)]"
      type Tup = Var[(ta.Typ,tb.Typ)]
      
      //val (a,b) = (ir"?a: Var[$ta]", ir"?b: Var[$tb]") // FIXME rewrite brittleness
      
      //val (ia,ib) = (ir"1",ir"2")
      //val (ia,ib) = init match { case ir"($a, $b)" => a -> b } // FIXME: Error:scala: unexpected UnApply
      //val (init_a,init_b) = tuple2Components(init)
      
      val initComps = tuple2Components(init)
      //show(initComps) // initComps =	Some((ir"1",ir"0")) : Option[scp.utils.->[FoldTupleVarOptim.this.base.Predef.IR[ta,<context @ 49:10>],FoldTupleVarOptim.this.base.Predef.IR[tb,<context @ 49:10>]]]
      
      val newBody = body topDown_rewrite {
        //case code"((${`tup`}:Tup) !)._1" => code"$a !" // TODO make it work – "EmbeddingException: Pattern shape not yet supported in rewrite rule: `tup`"
        case code"(($tu:Tup) !)._1" if tu =~= tup => code"$a !"
        case code"(($tu:Tup) !)._2" if tu =~= tup => code"$b !"
        case code"($tu:Tup) := ($va: $$ta, $vb: $$tb)" if tu =~= tup => code"$a := $va; $b := $vb"
        case code"($tu:Tup) !" if tu =~= tup => code"($a.!, $b.!)"
      } /* We cannot match with $tup because it is now a FV (see: new extracted binder semantics makes us remove the $ in `val tup` pattern)
           and FV matching is broken in the current IR; so have to go through this awkward matching mechanism. */
      
      //show(newBody)
      
      val newwBody2 = newBody subs 'tup -> {
        //println("ABORT!! "+newBody)
        throw RewriteAbort(s"tup is still used! in: $newBody")}
      
      //val newwBody2 = newBody subs 'tup -> ir"Var($a.!,$b.!)" // not what we want! this can be an invalid position for a Var
      //val newwBody2 = newBody subs 'tup -> ir"???"
      
      //show(newwBody2)
      //show(newwBody2 rep)
      //base.asInstanceOf[ANF].ANFDebug.debugFor{
      
      //ir""" val init = $init; val a = Var(init._1); val b = Var(init._2); $newwBody2 """
      //ir""" val init = $init; var a = init._1; var b = init._2; $newwBody2 """ // FIXME give right type to FV
      
      //println(ir"val a = Var(???); $newwBody2" rep)  // FIXME need for ta?
      //(ir"val a = Var[$ta](???); $newwBody2" rep) and (show(_)) // works
      //(ir"val b = Var[$tb](???); $newwBody2" rep) and (show(_)) // works
      //(ir"val u = 0; val v = 0; $newwBody2" rep) and (show(_)) // works
      //(ir"val a = Var[$ta](???); val b = Var[$tb](???); $newwBody2" rep) and (show(_)) // FIXME
      
      //(ir"val a = Var[$ta](???); val b = Var[$tb](???); ${ ir"while(true) { (?a: Var[$ta]):= ??? }" }" rep) and (show(_)) // works
      //(ir"val a = Var[$ta](???); val b = Var[$tb](???); ${ ir"while(true) { (?a: Var[$ta]):= ???;(?b: Var[$tb]):= ???; (?a: Var[$ta])->(?b: Var[$tb]) }" }" rep) and (show(_)) // works
      //(ir"val a = Var[$ta](???); val b = Var[$tb](???); ${ ir"val a = ?a: Var[$ta]; val b = ?b: Var[$tb]; while(true) { a:= ???;b:= ???; a->b }" }" rep) and (show(_)) // works
      /*
      //val a = ?a: Var[$ta]; val b = ?b: Var[$tb]
      val nbTexto = ir"""{
      val a = ?a: Var[Int]; val b = ?b: Var[Int]
  while ({
    val x_0: scala.Int = a.!;
    val x_1: scala.Int = b.!;
    val x_2: scala.Int = x_0.+(x_1);
    x_2.<(42)
  }) 
    {
      val x_3: scala.Int = a.!;
      val x_4: scala.Int = x_3.+(1);
      val x_5: scala.Int = b.!;
      val x_6: scala.Int = x_5.+(2);
      a.:=(x_4);
      b.:=(x_6)
    }
  ;
  val x_7: scala.Int = a.!;
  val x_8: scala.Int = b.!;
  scala.Tuple2.apply[scala.Int, scala.Int](x_7, x_8)
}"""
      (ir"val a = Var[Int](???); val b = Var[Int](???); $nbTexto" ) and (show(_)) // FIXME
      
      
      System exit 0
      */
      
      val res =
      initComps map (ab => code" val a = Var(${ab._1}); val b = Var(${ab._2}); $newwBody2 ") getOrElse
         code" val init = $init; val a = Var(init._1);  val b = Var(init._2);  $newwBody2 "
      
      //show(res rep)
      //show(res)
      res
      
      /* or equivalently: */
      
      /* FIXME: precise typing lost, probably because of rewrite's untypecheck */ 
      //initComps match {
      //  case Some((u,v)) => ir" val a = Var($u); val b = Var($v); $newwBody2 "
      //  case None => ir" val init = $init; val a = Var(init._1);  val b = Var(init._2);  $newwBody2 "
      //}
      
      
  }
  
  
  // Hackish workaround to inline FUnction2 that does not work:
  /*{
    import base._
    object Fun2 { def unapply(x: IR[_,_]) = x match {
      case IR(RepDef(Abs(Typed(p, TypeRep(RecordType(a->ta,b->tb))),body))) =>
        Some(a,b,body)
      case _ => None
    }}
    object Fun2App { def unapply(x: IR[_,_]) = x match {
      case ir"(${Fun2(a,b,body)}: (($tta,$ttb) => $t))($arg0,$arg1)" =>
        Some(a,b,body,arg0,arg1)
      case _ => None
    }}
    rewrite {
      // FIXME:
      case ir"((px: $tx, py: $ty) => $body: $t)($ax, $ay)" =>
        body subs 'px -> ax subs 'py -> ay
        // In the meantime:  
        //case ir"(${IR(RepDef(Abs(Typed(p, TypeRep(RecordType(a->ta,b->tb))),body)))}: (($tta,$ttb) => $t))($arg0,$arg1)" => // FIXME makes `rewrite` crash
      //case ir"(${Fun2(a,b,body)}: (($tta,$ttb) => $t))($arg0,$arg1)" => // FIXME makes `rewrite` crash: Error:scala: unexpected UnApply
      case ir"${Fun2App(a,b,body,arg0,arg1)}: $t" => // FIXME makes `rewrite` crash: Error:scala: unexpected UnApply
        IR[t.Typ,{}](bottomUpPartial(body) {
          case RepDef(RecordGet(re, `a`, _)) => arg0.rep
          case RepDef(RecordGet(re, `b`, _)) => arg1.rep
        })
    }
  }*/
  
}
object FoldTupleVarOptim {
  class ForNormDSL extends NormDSL.SelfTransformer with FoldTupleVarOptim
}
