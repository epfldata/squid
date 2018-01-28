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

import squid.lib.MutVar

/** Like the old FoldTupleVarOptim, but uses first-class variable symbols instead of hard-coded names. */
trait FoldTupleVarOptimNew extends FixPointRuleBasedTransformer with TopDownTransformer { self =>
  import base.Predef._
  import base.InspectableCodeOps
  import base.IntermediateCodeOps
  
  rewrite {
    
    case code"($ls: List[$ta]).foldLeft[$tb]($init)($f)" =>
      
      code""" var cur = $init
            $ls foreach { x => cur = $f(cur, x) }
            cur """
      
    case code"($ls: List[$t]) foreach ($f: t => Any)" =>
      
      code""" var iter = $ls
            while (iter.nonEmpty)
            { $f(iter.head); iter = iter.tail } """
      
    case code"($ls: List[$t]).foreach[$t2]($f)" => die  // the case above should always work (Any is in covariant position)
      
  }
  
  def tuple2Components[A:CodeType,B:CodeType,C](ab: Code[(A,B),C]): Option[ Code[A,C]->Code[B,C] ] = ab match {
    case code"($a:A, $b:B)" => Some(a -> b)
    case _ => None
  }
  
  rewrite {
    
    case code"val $tup = MutVar($init: ($ta, $tb)); $body: $t" =>
      
      val a = new Variable[MutVar[ta.Typ]]
      val b = new Variable[MutVar[tb.Typ]]
      
      val initComps = tuple2Components(init)
      
      val newBody = body topDown_rewrite {
        case code"($$tup !)._1" => code"$a !"
        case code"($$tup !)._2" => code"$b !"
        case code"$$tup := ($va: $$ta, $vb: $$tb)" => code"$a := $va; $b := $vb"
        case code"$$tup !" => code"($a.!, $b.!)"
      }
      
      val newwBody2 = tup.substitute[t.Typ, tup.OuterCtx & a.Ctx & b.Ctx](newBody, 
        Abort(s"tup=$tup is still used! in: $newBody"))
      
      val res = initComps.fold(
        code" val init = $init; val $a = MutVar(init._1);  val $b = MutVar(init._2);  $newwBody2 " )(ab =>
        code"                   val $a = MutVar(${ab._1}); val $b = MutVar(${ab._2}); $newwBody2 " )
      res
      
      /* FIXME: precise typing lost, probably because of rewrite's untypecheck:
       *   "Error: Cannot rewrite a term of context <context @ 58:10> to an unrelated context <context @ 58:10>" */ 
      //initComps match {
      //  case Some((u,v)) => ir" val $a = Var($u); val $b = Var($v); $newwBody2 "
      //  case None => ir" val init = $init; val $a = Var(init._1);  val $b = Var(init._2);  $newwBody2 "
      //}
      
  }
  
}
object FoldTupleVarOptimNew {
  class ForNormDSL extends NormDSL.SelfTransformer with FoldTupleVarOptimNew
}
