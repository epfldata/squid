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

package sfusion
package compiler

import java.io.File
import java.io.PrintStream

import squid.utils._
import squid.ir._
import squid.lang._
import squid.anf.analysis
import squid.anf.transfo

/*
  * TODO high-level optims such as map.map->map and map.flatten->flatMap; applying on the level of Sequence defs
  *   to work well this requires an effect system that accounts for latent effects,
  *     such that `s.map(a => a+readInt)` is pure but `s.map(a => a+readInt).fold(...)` is impure
  * 
  * TODO loop optims... can we match the pattern where the first iteration of the loop can be moved out?
  *   (a var starting true, set to false, with a comparison)
  *   as arises when concatenating a unary seq w/ another seq
  *   or just catch these earlier (convert `concat(single(.),.)` to `prepend(.,.)`) <- cleaner approach!
  * 
  */
class Compiler extends Optimizer {
  
  // TODO more settings
  /*
  val onOptimFailure: Option[(String,String) => Unit] = None
  val disableAssertions: Bool = false
  val outputDump: Option[String => File] = None
  val outputPrint: Option[PrintStream] = None
  */
  
  val base: Code.type = Code
  
  object Code
    //extends squid.ir.SimpleANF
    extends squid.ir.SchedulingANF
    with ScalaCore
    with ClassEmbedder with OnlineOptimizer with analysis.BlockHelpers with StandardEffects
  {
    object Desug extends Desugaring //with TopDownTransformer
    object Norm extends SelfTransformer with transfo.StandardNormalizer //with FixPointRuleBasedTransformer
    def pipeline = Desug.pipeline andThen Norm.pipeline
    
    embed(Sequence)
    embed(impl.`package`)
    
    import squid.utils.meta.RuntimeUniverseHelpers.sru
    transparentTyps += sru.typeOf[sfusion.`package`.type].typeSymbol.asType // for minSize, addToSize & co.
    
  }
  import Code.Predef._
  import Code.Quasicodes._
  
  val Impl = new Code.Lowering('Impl) with TopDownTransformer
  
  val Imperative = new Code.Lowering('Imperative) with FixPointTransformer with TopDownTransformer
    // ^ Note: needs fixed point because `fromIndexed` is implemented in terms of a direct call to `fromIndexedSlice`
  
  val LateImperative = new Code.Lowering('LateImperative) with TopDownTransformer
  
  val DCE = new Code.SelfTransformer with squid.anf.transfo.DeadCodeElimination
  
  val VarFlattening = new Code.SelfTransformer with transfo.VarFlattening with TopDownTransformer
  
  //val LowLevelNorm = new Code.SelfTransformer with LogicNormalizer with transfo.VarInliner with FixPointRuleBasedTransformer with BottomUpTransformer
  // ^ Some optimizations are missed even in fixedPoint and bottomUp order, if we don't make several passes:
  val LowLevelNorm = new Code.TransformerWrapper(
    // TODO var simplification here,
    new Code.SelfTransformer 
      with transfo.LogicNormalizer 
      with FixPointRuleBasedTransformer 
      with BottomUpTransformer { rewrite {
        case code"squid.lib.uncheckedNullValue[$t]" => nullValue[t.Typ]
      }}
  ) with FixPointTransformer
  
  //val HL = new Code.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer {
  val HL = new Code.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer {
    rewrite {
      // TODO: Q: make Sequence's map transparencyPropagating for this to work in more cases?
      // FIXME this does not handle other functions like filter, take/drop etc... 
      
      case code"($s: Sequence[$ta]).map[$tb]($f).map[$tc]($g)" =>
        code"$s.map($f andThen $g)"
        
      //case ir"val $ms = ($s: Sequence[$ta]).map[$tb]($f); $body: $bt" =>
      case code"($s: Sequence[$ta]).map[$tb]($f).flatMap[$tc]($g)" =>
        code"$s.flatMap($f andThen $g)"
        
      case code"($s: Sequence[$ta]).flatMap[$tb]($f).flatMap[$tc]($g)" =>
        code"$s.flatMap($f(_) flatMap $g)"
        
    }
  }
  
  val CtorInline = new Code.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer {
    rewrite {
      case code"val $s = new Sequence[$ta]($under,$size); $body: $bt" =>
        val underFV = code"?under: (() => impl.Producer[$ta])"
        val sizeFV = code"?size: SizeInfo"
        val body2 = body rewrite {
          case code"$$s.under" => underFV
          case code"$$s.size" => sizeFV
        }
        
        //val body3 = body2 subs 's -> Abort()
        val body3 = s.substitute[bt.Typ, s.OuterCtx & underFV.Ctx & sizeFV.Ctx](body2, Abort())
        
        code"val under = $under; val size = $size; $body3"
    }
  }
  
  val ImplOptim = new Code.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer {
    import impl._
    
    // Q: works with hygienic context polym?!
    // TODO generalize for any associative binop;
    // Note: this would be best achieved by simply re-associating to the right all associative binops
    /** Extracts the right-hand side of some string addition starting with free variable `acc?:String`.
      * This is useful because currently pattern `acc + $x` cannot match something like `(acc + a) + b`. */
    object StringAccAdd {
      val Acc = code"?acc:String"
      // ^ Note: inline `${ir"acc?:String"}` in the pattern is mistaken for an xtion hole (see github.com/LPTK/Squid/issues/11)
      def unapply[C](x:Code[Any,C]): Option[Code[Any,C]] = x match {
        case code"($Acc:String) + $rest" => Some(rest)
        case code"($lhs:String) + $rhs" => unapply(lhs) map (x => code"$x.toString + $rhs") orElse (unapply(rhs) map (x => code"$lhs + $x"))
        case _ => None
      }
    }
    
    rewrite {
      case code"fold[String,String]($s)($z)((acc,s) => ${StringAccAdd(body)})" => // TODO generalize... (statements?!)
        val strAcc = code"?strAcc: StringBuilder"
        val body2 = body subs 'acc -> code"$strAcc.result"
        val zadd = if (z =~= code{""}) code"()" else code"$strAcc ++= $z" // FIXME does not compile when inserted in-line... why?
        code"val strAcc = new StringBuilder; $zadd; foreach($s){ s => strAcc ++= $body2.toString }; strAcc.result"
    }
    
    //object Linear {
    //  // TODO use
    //  //def unapply[C](x:IR[Any,C]): Option[IR[  ,C]] = 
    //}
    //
    //rewrite {
    //  case ir"val $ts = fromIndexed[$t]($indexed); $body: $bt" =>
    //    val body2 = body rewrite {
    //      case ir"flatMap($$ts, )"
    //    }
    //    body2
    //}
    
  }
  object ImplFlowOptimizer extends Code.SelfTransformer with ImplFlowOptimizer
  
  //val FlatMapFusion = new Code.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer {
  val FlatMapFusion = new Code.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer {
    import impl._
    import Code.Closure
    
    rewrite {
      case code"flatMap[$ta,$tb]($s)(a => ${Closure(clos)})" =>
        //println("CLOS: "+clos)
        import clos._
        import squid.lib.Var
        
        println(fun)
        //val fun2 = fun subs 'a -> Abort()
        //val fun2 = fun subs 'a -> ???
        val fun2 = fun subs 'a -> code"(?aVar: Var[Option[$ta]]).!.get"
        // ^ TODO could save the 'a' along with the environment...
        // ... when more methods are pure/trivial, it may often happen (eg `stringWrapper` that makes String an IndexedSeq)
        
        // Reimplementation of flatMap but using a variable for the Producer state and _not_ for the Producer, so it can be inlined.
        // Note: would probably be simpler to implement it in shallow as syntax sugar to use from here.
        //  var aVar: Option[$ta] = None // FIXME allow this syntax...
        val res = code"""
          val s = $s
          val aVar = Var[Option[$ta]](None)
          var envVar: Option[E] = None
          (k => {
            var completed = false
            var continue = false
            while({
              if (envVar.isEmpty) s { a => aVar := Some(a); envVar = Some($env); false }
              if (envVar.isEmpty) completed = true
              else {
                if ($fun2(envVar.get) { b => continue = k(b); continue }) envVar = None
              }
              !completed && continue
            }){}
            completed
          }) : Producer[${tb}]
        """
        
        // cleanup could be done here, but will be done in next `VarFlattening` phase anyways
        //val res2 = res transformWith (new Code.SelfTransformer with transfo.VarFlattening with TopDownTransformer)
        
        res
        
    }
  }
  
  
  def dumpPhase(name: String, code: => String, time: Long) = {
    println(s"\n === $name ===\n")
    println(code)
  }
  
  import Code.Rep
  
  val phases: List[String->(Rep=>Rep)] = List(
    "HL" -> HL.pipeline,
    "Impl" -> Impl.pipeline,
    "CtorInline" -> CtorInline.pipeline,
    //"DCE 0" -> DCE.pipeline,  // FIXME only remove effectless/just-read things
    "ImplOptim" -> ImplOptim.pipeline,
    //"ImplFlowOptimizer" -> ImplFlowOptimizer.pipeline,
    "Imperative" -> Imperative.pipeline,
    "FlatMapFusion" -> FlatMapFusion.pipeline,
    "LateImperative" -> LateImperative.pipeline,
    "VarFlattening" -> VarFlattening.pipeline,
    "Low-Level Norm" -> LowLevelNorm.pipeline,
    "ReNorm (should be the same)" -> ((r:Rep) => base.reinterpret(r, base)())
    //"ReNorm (should be the same)" -> ((r:Rep) => base.reinterpret(r, base)().asInstanceOf[base.Rep] |> base.Norm.pipeline)
  )
  
  protected val SAME = "[Same]"
  
  def pipeline = (r: Rep) => {
    
    dumpPhase("Init", base.showRep(r), 0)
    
    phases.foldLeft(r) { case (r0, name -> f) =>
      val t0 = System.nanoTime()
      val r1 = f(r0)
      val t1 = System.nanoTime()
      dumpPhase(name, if (r1 =~= r0) SAME else base.showRep(r1), t1-t0)
      r1
    }
    
    
  }
  
  var curId = Option.empty[String]
  override def wrapOptim[A](id: String)(code: => A) = {
    curId = Some(id)
    try super.wrapOptim(id)(code) finally curId = None
  }
  
}


