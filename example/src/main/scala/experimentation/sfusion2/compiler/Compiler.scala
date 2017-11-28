package sfusion2
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
import Embedding.{Block, AsBlock, WithResult, GeneralClosure}
//import Embedding.{Block, AsBlock, WithResult, GeneralClosure, ConstantShape}

/*

TODO: 
find a better way to deal with the options
  when using default doWhile implem (eg on: ir{ (xss: IndexedSeq[IndexedSeq[Int]]) => fromIndexed(xss).flatMap(fromIndexed).map(_ + 1).fold(0)(_ + _) })
  we end up with tons of stupid inter-mixing of options and if-then-else
  A CPS ecoding of options would probably sove the issue to some extent  

Note: two ways to solve zip(flat,flat)
  LL way: detect function option variables with single shape
  HL way: more algebraic rewriting


The gist of the idea:
we normalize/order all operations so that:
 - flatten or filter followed by drop/take is at the end of any nested thingy
 - we merge map on flatten into the left of the flatten
 - drop/take are as far at the beginning as possible
 - put drop at the left of take
 - take/drop are extracted from zipWith args


call doFold on staged stream to form neat loops and proper zippings

ideally: try to do 2-ways fusion, of consumers AND producers
  Q: is that really helpful? -> I think depending on the programs, yes

*/

/*

trait StagedStrm[A,C]
case class LinearStrm[A,C](p: IR[Producer[A],C]) extends StagedStrm[A,C]
case class NestedStrm[A,B,C](p: IR[Producer[A],C], f: A => StagedStrm[B,C]) extends StagedStrm[B,C]
/** For streams which shape could not be determined at compile/staging time */
case class DynamicStrm[A,C](/* ??? */) extends StagedStrm[B,C]

*/

/**
  * Created by lptk on 13/06/17.
  */
class Compiler extends Optimizer {
  
  val base: Embedding.type = Embedding
  
  /*
  def stage[A,C](strm: IR[Strm[A],C]): StagedStream[A] = strm match {
    case ir"Strm(() => prod)" => // for sources (will be inlined); eg: `fromIndexed` 
  }
  def doFold[A,R,C](sstrm: StagedStrm[Strm[A],C], z: R, f: (R,A) => R): IR[R,C] = sstrm match {
    case LinearStrm(p) => ir"linearFold($p,$z,$f)"
    case _ => ???
  }
  
  rewrite {
    case ir"($strm: Strm[$ta]).fold[$tb]($z)($f)" => // TODO use a generic Fold xtor...
      doFold(stage(strm), z, f)
  }
  */
  
  
  def pipeline = (r: Rep) => {
    //val r0 = Embedding.debugFor (ImplFlowOptimizer pipeline r)
    val r0 = ImplFlowOptimizer pipeline r
    println("--- ImplFlowOptimizer ---\n"+r0)
    
    //val r1 = ImplFold pipeline r0
    val r1 = ImplFold pipeline (FoldInlining pipeline r0)
    println("--- ImplFold ---\n"+r1)
    
    val r2 = ImplLowering pipeline r1
    //val r2 = r1
    println("--- ImplLowering ---\n"+r2)
    //r2
    
    //val r3 = CtorInline pipeline r1
    //r3
    
    ////val r3 = LowLevelNorm pipeline (VarFlattening pipeline r2) // FIXME probably crashes because pattern norm is on
    //val r3 = LowLevelNorm pipeline (/*VarFlattening pipeline*/ r2)
    //println("--- Low Level ---\n"+r3)
    //r3
    
    val r3 = Flow pipeline r2
    println("--- Logic Flow ---\n"+r3)
    r3
    
  }
  
}




import Strm._
import Embedding.Predef._

object ConstantShape {
  //def unapply[T:CodeType,C](x: IR[Strm[Strm[T]],C]): Option[IR[Strm[T],C]] = x match {
  def unapply[T:CodeType,C](x: Code[Strm[T],C]): Option[Code[Strm[T],C]] = x match {
    //case GeneralClosure(clos) =>
    //  println(x)
    //  println(clos)
    //  ???
    case AsBlock(bl) =>
      println(bl.res)
      bl.res match {
        case code"fromIndexed($fi)" => println("!! "+fi)
        case _ => //return None
      }
      ???
  }
}
//class ConstantShape[](val env: E)
abstract class ConstantShape[A,-C] {
  type E
  val env: Code[E,C]
  val fun: Code[E => A,C]
  implicit val typA: CodeType[A]
  implicit val typE: CodeType[E]
}
private case class ConstantShapeImpl[A,C,TE](env: Code[TE,C], fun: Code[TE => A,C])(implicit val typA: CodeType[A], val typE: CodeType[TE])
  extends ConstantShape[A,C] { type E = TE }

/*
abstract class StagedProducer[+A,-C] {
  // takes a producer of A's, makes a producer that consumes from it and resets as needed 
  
  val step: IR[() => Option[A],C]
  val restart: IR[X => Unit,C]
  def map[B](f: IR[A => B,C]): StagedProducer[B,C]
}
//case class IndexedProducer[+A,-C](step: IR[() => Option[A],C]) extends StagedProducer[A,C] {
case class IndexedProducer[+A,-C]() extends StagedProducer[A,C] {
  def map[B](f: IR[A => B,C]): IndexedProducer[B,C]
}
*/


// An approach with Env as below needs placeholders unless we have context polymorphism... so it's probably simpler to go with object-lang functions, following Wadler & al
/*
abstract class StagedProducer[+A,-C] { parent =>
  type Env
  val init: Env => IR[Unit,C]
  val step: Env => IR[Option[A],C]
  def make[R](code: (Env => IR[R,C])): IR[R,C] //= code()
  
  def take(n: IR[Int,C]) = new StagedProducer[A,C] {
    type Env = (parent.Env, IR[Var[Int]])
    def make[R](code: (Env => IR[R,C])): IR[R,C] = parent.make(e => code(e,))
  }
  //def map[B](f: IR[A => B,C]): StagedProducer[B,C]
}
case class IndexedProducer[+A,-C](xs: IR[IndexedSeq[A],C]) extends StagedProducer[A,C] {
  type Env = (IR[Var[Int]])
  val init = e => ir"$e := 0"
  val step = e => ir"val i = $e.!; if (i < $xs.length) { val r = $xs(i); $e := i+1; r } else None"
  def make[R](code: (Env => IR[R,C])): IR[R,C] = {
    ir"val i = 0; ${code(ir"i?:Int")}"
  }
  
  //def map[B](f: IR[A => B,C]): IndexedProducer[B,C]
}
*/
import squid.lib.Var
abstract class StagedProducer[+A:CodeType,C] { parent =>
  type Env[+R]
  implicit def EnvType[R:CodeType]: CodeType[Env[R]]
  def mapEnv[A:CodeType,B:CodeType](e: Code[Env[A],C], f: Code[A => B,C]): Code[Env[B],C] // TODO impl
  //def mapEnv2[A:CodeType,B:CodeType](e: IR[Env[A],C])(f: IR[A => B,C]): IR[Env[B],C] = mapEnv(e,f) // TODO rm
  def liftEnv[A](a: Code[A,C]): Code[Env[A],C]
  //def flatMapEnv
  //def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](lhs: IR[Env[A],C], rhs: IR[Env[B],C])(combine: IR[(A,B)=>R,C]): IR[Env[R],C]
  def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](combine: Code[(A,B)=>R,C]): Code[(Env[A],Env[B])=>Env[R],C]
  //def flatMapEnv[A:CodeType,B:CodeType](lhs: IR[Env[A],C], rhs: IR[Env[B],C]): IR[Env[A -> B],C]
  
  //val init: IR[Env => Unit,C]
  //val step: IR[Env => Option[A],C]
  val init: Code[Env[Unit],C]
  val step: Code[Env[Option[A]],C]
  //val init_step: IR[Env[Unit -> Option[A]],C]
  //val fail: IR[Env[None.type],C]
  def make[R:CodeType](code: Code[Env[R],C]): Code[R,C]
  //def make2[R:CodeType](code: IR[(() => Unit, () => Option[A]) => R,C]): IR[R,C] = ir{ val ab = $(flatMapEnv(init,step)); $(code)(ab._1,ab._2) }
  def make2[R:CodeType](code: Code[(() => Unit, () => Option[A]) => R,C]): Code[R,C] = 
    //flatMapEnv(init,step)(code)
    //flatMapEnv(mapEnv2(init)(ir{x => () => x}),???)(code)
    //make(flatMapEnv(mapEnv(init,ir{(x:Unit) => () => x}),mapEnv(step,ir{(x:Option[A]) => () => x}))(code))
    //make(ir{$(flatMapEnv(code))(() => $(init),() => $(step))})
  {
    val in = mapEnv(init,ir{(x:Unit) => () => x})
    val st = mapEnv(step,ir{(x:Option[A]) => () => x})
    make(ir{$(flatMapEnv(code))($(in),$(st))})
  }
  
  def take(n: Code[Int,C]): StagedProducer[A,C] = new StagedProducer[A,C] {
    import parent.{EnvType => parentEnvType}
    //implicit def parentEnvType[R:CodeType]: CodeType[parent.Env[R]] = ??? // FIXME
    
    type Env[+R] = Var[Int] => parent.Env[R] // Q: what about parent.Env[Var[Int] => R] ?
    //implicit def EnvType[R]: CodeType[Env[R]] = ??? // FIXME
    implicit def EnvType[R:CodeType]: CodeType[Env[R]] = ??? // FIXME
    //def EnvType[R:CodeType]: CodeType[Env[R]] = ??? // FIXME
    def mapEnv[A:CodeType,B:CodeType](e: Code[Env[A],C], f: Code[A => B,C]): Code[Env[B],C] = ???
    def liftEnv[A](a: Code[A,C]): Code[Env[A],C] = ir[Env[A]]{ _ => $(parent.liftEnv(a)) }
    //def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](lhs: IR[Env[A],C], rhs: IR[Env[B],C])(combine: IR[(A,B)=>R,C]): IR[Env[R],C] = 
    //  ir{(v:Var[Int]) => $(parent.flatMapEnv(lhs,rhs)())} ...
    def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](combine: Code[(A,B)=>R,C]): Code[(Env[A],Env[B])=>Env[R],C] =
      ir{(ea:Env[A],eb:Env[B]) => (v:Var[Int]) => $(parent.flatMapEnv(combine))(ea(v),eb(v))}
    
    implicit val WAT = parentEnvType[Unit]
    implicit val WAT2 = parentEnvType[Option[A]]
    //Embedding.Predef.dbg.implicitType[parent.Env[Unit]]
    
    val init = ir[Env[Unit]]{ e => e := 0; $(parent.init) }
    //val step = ir"e => { val i = e.!; if (i < $xs.length) { val r = $xs(i); e := i+1; r } else None }"
    //val step = ir[Env[Option[A]]]{ e => val taken = e.!; if (taken < $(n)) { e := taken + 1; $(parent.step) } else $(parent.fail) }
    val step = ir[Env[Option[A]]]{ e => val taken = e.!; if (taken < $(n)) { e := taken + 1; $(parent.step) } else $(parent.liftEnv(code"None")) }
    //val init_step = ir[Env[Unit -> Option[A]]]{ e =>  }
    //val fail = ir[Env[None.type]]{ _ => $(parent.fail) }
    //def make[R](code: IR[Env[R],C]): IR[R,C] = parent.make(ir"$code(Var(0))")
    def make[R:CodeType](code: Code[Env[R],C]): Code[R,C] = parent.make(code"val vtaken = Var(0); $code(vtaken)")
  }
  
  def map[B:CodeType](f: Code[A => B,C]): StagedProducer[B,C] = new StagedProducer[B,C] {
    type Env[+R] = parent.Env[R]
    implicit def EnvType[R:CodeType]: CodeType[Env[R]] = parent.EnvType[R]
    def mapEnv[A:CodeType,B:CodeType](e: Code[Env[A],C], f: Code[A => B,C]): Code[Env[B],C] = parent.mapEnv(e,f)
    def liftEnv[A](a: Code[A,C]): Code[Env[A],C] = parent.liftEnv(a)
    def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](combine: Code[(A,B)=>R,C]): Code[(Env[A],Env[B])=>Env[R],C] = parent.flatMapEnv(combine)
    
    val init = parent.init
    //val step = ir{ $(parent.step) map $f }
    //val step = mapEnv[Option[A],Option[B]](parent.step, ir{ _ map f })
    val step = mapEnv(parent.step, ir{ (_:Option[A]) map $(f) })
    //val fail = parent.fail
    def make[R:CodeType](code: Code[Env[R],C]): Code[R,C] = parent.make(code)
  }
}
case class IndexedProducer[+A:CodeType,C](xs: Code[IndexedSeq[A],C]) extends StagedProducer[A,C] {
  type Env[+R] = Var[Int] => R
  //implicit def EnvType[R]: IRType[Env[R]] = { val EnvType = 0; implicitly }
  //implicit def EnvType[R]: IRType[Env[R]] = { import IndexedProducer.this.{EnvType => _}; implicitly }
  //def EnvType[R]: IRType[Env[R]] = ??? //implicitly // FIXME
  def EnvType[R:CodeType]: CodeType[Env[R]] = implicitType[Env[R]]
  def mapEnv[A:CodeType,B:CodeType](e: Code[Env[A],C], f: Code[A => B,C]): Code[Env[B],C] = ir[Env[B]]{ v => $(f)($(e)(v)) }
  def liftEnv[A](a: Code[A,C]): Code[Env[A],C] = ir[Env[A]]{ _ => $(a) }
  def flatMapEnv[A:CodeType,B:CodeType,R:CodeType](combine: Code[(A,B)=>R,C]): Code[(Env[A],Env[B])=>Env[R],C] =
    ir{(ea:Env[A],eb:Env[B]) => (v:Var[Int]) => $(combine)(ea(v),eb(v))}
  
  val init = ir[Env[Unit]]{ e => e := 0 }
  val step = ir[Env[Option[A]]]{ e => { val i = e.!; if (i < $(xs).length) { val r = $(xs)(i); e := i+1; Some(r) } else None } }
  //val fail = ir[Env[None.type]]{ _ => None }
  def make[R:CodeType](code: Code[Env[R],C]): Code[R,C] = code"val vi = Var(0); $code(vi)"
  
  //def map[B](f: IR[A => B,C]): IndexedProducer[B,C]
}
object StagedProducer {
  def unapply[T:CodeType,C](x: Code[Strm[T],C]): Option[StagedProducer[T,C]] = x match {
    //case AsBlock(bl) => // TODO use, need to aggregate local environment...
    case code"fromIndexed[T]($xs)" =>
      //println("!! "+fi)
      //???
      Some(IndexedProducer(xs))
    case code"($as:Strm[$ta]).map[T]($f)" =>
      unapply(as) map (_ map f)
    case _ => None
  }
}
// ^ doesn't work (can't make step/init capture `a` in the progrma made by `make`)
// TODO use HOAS again, but use safeSubs to `make` the code; which calls a function with a placeholder and _then_ replacers the latter with a given FV




/*

TODO
  zip(filter(xs),ys) -> filter(zip(xs,ys)) ?
  



fromIndexed(xs):
  state: var i, val len
  reset: i = 0, len = xs.length
  step: if (i < len) Some(xs(i++)) else None
fromIndexed(xs).take(n):
  state: var i, val len, var taken
  reset: i = 0, len = xs.length, taken = 0
  step: if (taken < n) (if (i < len) Some(xs(i++)) else None) else None
fromIndexed(xs).take(n).map(f):
  state: idem
  reset: idem
  step: (if (taken < n) (if (i < len) Some(xs(i++)) else None) else None) map f




  
*/
//object ImplFlowOptimizer extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer with FixPointTransformer { self =>
object ImplFlowOptimizer extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with TopDownTransformer with FixPointTransformer { self =>
  
  object NotFlattened {
    //def unapply[T,C](x: Code[T,C]): Option[Code[T,C]] = x match {
    //def unapply[T,C](x: IR[Strm[T],C]): Option[IR[T,C]] = x match {
    def unapply[T,C](x: Code[Strm[T],C]): Option[Code[Strm[T],C]] = x match {
      case code"flatten[$t]($strm)" => None
      case _ => Some(x)
    }
  }
  object Resumable {
    def unapply[T,C](x: Code[Strm[T],C]): Option[Code[Strm[T],C]] = x match {
      case _ => ???
    }
  }
  // eg: flatten(fromIndexed(strs).drop(1).map{s => val rs = richString(s); fromIndexed(rs)})
  //             ^ Resumable()
  //object Linearized {
  //  def unapply[T,C](x: IR[Strm[Strm[T]],C]): Option[IR[Strm[T],C]] = x match {
  //    case ir"(${Resumable(as)}:Strm[$ta]).map($f)" =>
  //      ???
  //  }
  //}
  
  rewrite {
      
    case code"($as: Strm[$ta]).map[$tb]($f).take($n)" =>
      code"$as.take($n).map[$tb]($f)"
      
    case code"($as: Strm[$ta]).map[$tb]($f).drop($n)" =>
      code"$as.drop($n).map[$tb]($f)"
      
    case code"($as: Strm[$ta]).take($n).take($m)" =>
      code"$as.take($n max $m)"
      
    case code"($as: Strm[$ta]).take($n).drop($m)" =>
      code"$as.drop($m).take($n - $m)" // FIXME careful with drop(-n) ... normally valid
      
    case code"($as: Strm[$ta]).drop($n).drop($m)" =>
      code"$as.drop($n + $m)"
      
    // THIS should be on:
    case code"flatten(($as: Strm[Strm[$ta]])).map[$tb]($f)" =>
      //ir"$as.map(_.map($f)).flatten"
      code"flatten($as.map(_.map($f)))"
    //case ir"flatten(($as: Strm[Strm[$ta]]).map[Strm[$tb]](nope => nope.map[tb]($f)))" => // probably not a good idea
    //  ???
    //  ir"flatten($as).map[$tb](${f subs 'nope -> Abort()})"
      
    case code"($as: Strm[$ta]).map[$tb]($fb).map[$tc]($fc)" =>
      code"$as.map($fb andThen $fc)"
      
      
      
    ////case ir"flatten(($as: Strm[$ta]).map[Strm[$tb]](a => ${ConstantShape(cs)}))" => // FIXME bad compile errors when `ConstantShape` wrongly requires Strm[Strm[T]]
    //case ir"flatten[tb](($as: Strm[$ta]).map[Strm[$tb]]((a:ta) => ${ConstantShape(cs)} : Strm[tb]))" =>
    ////case ir"flatten(($as: Strm[$ta]).map[Strm[$tb]](a => ${GeneralClosure(cs)}))" =>
    //  //ir"flatten($as.map(_.map($f)))"
    //  ???
      
      
      
    //case ir"($as: Strm[$ta0]).map[$ta1]($fa).zipWith(($bs: Strm[$tb0]).map[$tb1]($fb))($f)" =>
    //  ir"$as.zipWith($bs)((a,b) => $f($fa(a),$fb(b)))"
    //case ir"($as: Strm[$ta0]).map[$ta1]($fa).zipWith($bs: Strm[$tb0])($f)" =>
    case code"($as: Strm[$ta0]).map[$ta1]($fa).zipWith[$tb0,$tc]($bs)($f)" =>
      code"$as.zipWith($bs)((a,b) => $f($fa(a),b))"
    //case ir"($as: Strm[$ta0]).zipWith(($bs: Strm[$tb0]).map[$tb1]($fb))($f)" =>
    //case ir"($as: Strm[$ta0]).zipWith[$tb1,$tc](($bs: Strm[$tb0]).map[tb1]($fb))($f)" =>
    case code"($as: Strm[$ta0]).zipWith[$tb1,$tc](($bs: Strm[$tb0]).map[tb1]($fb))($f)" => // TODO warn that without `tb1` we infer Nothing...
      //???
      code"$as.zipWith($bs)((a,b) => $f(a,$fb(b)))"
      
    // ^ seems to make no difference with end code for simple pipeline, but at least should lessen the work of the normalizer
      
    case code"($as: Strm[$ta]).take($n).zipWith[$tb,$tc]($bs)($f)" =>
      code"($as: Strm[$ta]).zipWith[$tb,$tc]($bs)($f).take($n)"
    // TODO do something for drop? also for bs
      
    
    
      
    //case ir"flatten($as: Strm[$ta]).zipWith[$tb,$tr]($bs)($f)" =>
    case code"flatten($as: Strm[Strm[$ta]]).zipWith[$tb,$tr](${NotFlattened(bs)})($f)" => // putting nested streams on the right
      code"$bs.zipWith(flatten($as))((b,a) => $f(a,b))"
    
      
    // wrong:
    //case ir"($as: Strm[$ta]).zipWith[$tb,$tr](flatten[tb]($bs))($f)" => // FIXME use ${NotFlattened(as)} ?
    //  ir"flatten($bs.map($as.zipWith(_)($f)))"
    
    
    
    
  }
  
}

// TODO use custom xtors like Nested(_) instead of flatten(_); should match flatten(_), flatten(_).drop, etc.
object ImplFold extends Embedding.SelfTransformer with FixPointRuleBasedTransformer with BottomUpTransformer with FixPointTransformer { self =>
  
  rewrite {
    
    //case ir"Strm($pf).producer" => pf
    //case ir"val $st = Strm[$t]($pf); $body: $bt" =>
    //  body rewrite { case ir"$$st.producer" => pf } subs 'st -> {System.err.println("huh s");Abort()}
      
    //case ir"flatten(($ass: Strm[Strm[$ta]]).map[$tb]($fb)).doWhile($fw)" =>
    case code"flatten(($as: Strm[$ta]).map[Strm[$tb]]($fb)).doWhile($fw)" =>
      //ir"""
      //  val p = producer()
      //  Strm.loopWhile {
      //    val elt = p()
      //    elt foreach f
      //    elt.isDefined
      //  }
      //"""
          //as.map(fb)
      //ir"""
      //  $ass.doWhile { as =>
      //    $fb(as) doWhile $fw
      //  }
      //"""
      code"""
        $as.doWhile { a =>
          $fb(a) doWhile $fw
        }
      """
      
    case code"($as: Strm[$ta]).map[$tb]($fb).doWhile($fw)" =>
      code"$as.doWhile($fb andThen $fw)"
      
    case code"($as: Strm[$ta]).take($n).doWhile($fw)" =>
      code"var taken = 0; $as.doWhile { x => taken += 1; taken <= $n && $fw(x) }; true"
      
    case code"($as: Strm[$ta]).drop($n).doWhile($fw)" =>
      //ir"val dropped = 0; $as.doWhile { x => if (dropped >= $n) $fw(x) else dropped += 1 }"
      code"var dropped = 0; $as.doWhile { x => if (dropped < $n) { dropped += 1; true } else $fw(x) }; true"
      
    case code"fromIndexed($xs: IndexedSeq[$ta]).doWhile($fw)" =>
      //ir"val len = $xs.length; var i = 0; loopWhile { val inbound = i < len; i +=  && $fw() }"
      
      // pretty much similar, but the former puts more stuff in the if block:
      code"val len = $xs.length; var i = 0; loopWhile { i < len && { val x = $xs(i); i += 1; $fw(x) } }; true"
      //ir"val len = $xs.length; var i = -1; loopWhile { i += 1; i < len && $fw($xs(i)) }; true"
      
    case code"fromIterable($xs: Iterable[$ta]).doWhile($fw)" =>
      code"val it = $xs.iterator; loopWhile { it.hasNext && $fw(it.next) }; true"
      
    // FIXME returning true in the above correct?!
    
    
    
    /*
    case ir"(flatten($as:Strm[Strm[$ta]])).zipWith[$tb,$tc](flatten($bs:Strm[Strm[tb]]))($f).doWhile($fw)" =>
      //ir"val pa = $as.producer(); val pb = $bs.producer(); "
      ir"flatflatdoWhile($as,$bs)((a,b) => $fw($f(a,b)))"
      //ir"flatflatdoWhile($as,$bs)((a:$ta,b:$tb) => $fw($f(a,b)))"

    //case ir"flatflatdoWhile[$ta,$tb,$tc]($as,$bs)($f)" =>
    //case ir"flatflatdoWhile[$ta,$tb,$tc](($as:Strm[Strm[$ta0]]).map[Strm[$ta]](_.map($f)),$bs)($fw)" =>
    case ir"flatflatdoWhile[$ta,$tb,$tc](($as:Strm[$ta0]).map[Strm[ta]]($f),$bs)($fw)" =>
      ???
    */
      
      
    case code"($as: Strm[$ta]).zipWith[$tb,$tc]($bs)($f).doWhile($fw)" =>
      //ir"val p = $bs.producer(); $as.doWhile(a => p().fold(false){ b => $fw($f(a,b)) })"
      code"val p = $as.producer(); $bs.doWhile(b => p().fold(false){ a => $fw($f(a,b)) })"
      
      
      
    ////case ir"($as: Strm[$ta0]).map[$ta1]($fa).zipWith(($bs: Strm[$tb0]).map[$tb1]($fb))($f).doWhile($fw)" =>
      
    //case ir"flatten($as: Strm[Strm[$ta]]).zipWith[$tb]($bs)($f).doWhile($fw)" =>
    //  ir"flatten($as.map(_.map(a => $f(a,)))).doWhile($fw)"
      
    //case ir"flatten($as: Strm[Strm[$ta]]).zipWith[$tb]($bs)" =>
    //  ir"val p = $bs.producer; $as.map()"
    
    
    
    
    //case ir"flatten[tb](($as: Strm[$ta]).map[Strm[$tb]]((a:ta) => ${ConstantShape(cs)} : Strm[tb]))" =>
    case code"flatten[tb](($as: Strm[$ta]).map[Strm[$tb]]((a:ta) => ${StagedProducer(cs)} : Strm[tb]))" =>
      import cs._
      
      //ir"flatConst[$ta,E,$tb]($as, a => $env, (a,e) => $fun(e))"
      
      //ir"Strm(() => { val pas = $as.producer(); val pb = stageprod; () => {  } })"
      
      //println(cs.make(cs.liftEnv(ir"println(${cs.step})")))
      //println(cs.make(cs.step))
      //println(cs.make(cs.mapEnv2(cs.step)(ir{step => Left(step)})))
      //println(cs.make(cs.mapEnv2(cs.step)(ir"(step:Option[$tb]) => Left(step)")))
      
      println(cs.make2(code"{(init:()=>Unit,step:()=>Option[$tb]) => if (readInt>0) init(); step()}")) // FIXME
      
      //??? // TODO
      
      //val a = ir"a?:Var[$ta]"
      
      val prod =
      //cs.make2(ir"""{ (init: ()=>Unit, step: ()=>Option[$tb]) =>
      //  Strm[$tb](() => () => { while(0.toDouble<0){init()}; step() })
      //}""")
          //while(0.toDouble<0){init()}; step()
        //var a: Option[$ta] = None
      cs.make2(code"""{ (init: ()=>Unit, step: ()=>Option[$tb]) =>
        val p = $as.producer()
        var curA: Option[$ta] = None
        () => {
          var curB: Option[$tb] = None
          loopWhile {
            //val a = 
            curA orElse {
              val a = p()
              init()
              curA = a
              a
            }
            curA.fold(false){ a =>
              curB = step()
              true
            }
            if (curB.isDefined) { false } else { curA = None; true }
          }
          curB
        }
      }""")
      
      val r = code"Strm[$tb](() => $prod)"
        
      println(r)
      
      //println(r.reinterpretIn(Embedding))
      
      //???
      r subs 'a -> {System.err.println("eeeh");Abort()}
    
    
    
    
    
  }
  
}

object FoldInlining extends Embedding.Lowering('Fold) with TopDownTransformer //with FixPointTransformer

//object ImplLowering extends Embedding.Lowering('Impl) with TopDownTransformer
object ImplInlining extends Embedding.Lowering('Impl)
object ImplCtorInline extends Embedding.SelfCodeTransformer with CodeTransformer with FixPointTransformer {
  def transform[T,C](code: Code[T,C]): Code[T,C] = (code match {
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


