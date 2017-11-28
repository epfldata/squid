package sfusion

import org.scalatest.FunSuite
import squid.TestDSL
import squid.ir._
import squid.utils._

/**
  * Created by lptk on 07/02/17.
  */
class OptimTests extends FunSuite {
  
  object Compiler extends compiler.TestCompiler
  import Compiler.Code.Predef._
  import Compiler.Code.Quasicodes._
  Compiler.Code.embed(algo.`package`)
  
  test("Basics") {
    
    //val c0 = ir"Sequence(1,2,3,4)" // FIXME handle varargs in @embed...
    
    val c0 = code"Sequence.fromIndexed(1 to 10).toString"
    
    val res = "Sequence(1,2,3,4,5,6,7,8,9,10)"
    assert(c0.run == res)
    
    val c1 = Compiler.wrapOptim("Basics") {
      Compiler.optimize(c0)
    }
    
    //assert(c1.run == res) // the hacky InterpreterBase has problems with by-name parameters due to Scala reflexion limitations... (here affecting squid.lib.And)
    assert(c1.compile == res)
    
  }
  
  test("Sieve") {
    
    val c0 = ir{algo.primeSum(100)}
    assert(c0.run == 101)
    
    val res = Compiler.wrapOptim("Sieve") {
      val r = Compiler.optimize(c0)
      //println(r.rep)
      //println(r.run)  // FIXME: expected a member of class Boolean, you provided method squid.lib.And
    }
    
  }
  
  
  test("Join Lines") {
    
    val ls = List("lol","okay","test")
    val res = "lol\nokay\ntest"
    
    val c0 = ir{algo.joinLinesSimple(_:Iterable[String])}
    val r0 = algo.joinLinesSimple(ls)
    
    assert(r0 == res)
    assert((ls |> c0.run) == r0)
    
    Compiler.wrapOptim("JoinLines") {
      
      // Note: for some reason, `transfo.IdiomsNormalizer` does not seem to eliminate extra `toString` calls,
      // despite that transformer working well on simple examples as in `NormalizationTests`.
      // This might indicate a subtle typing problem, to investigate...
      
      val r = Compiler.optimize(c0)
      assert((ls |> r.run) == r0)
      // ^ Note: when not inlined completely, `run` throws: scala.ScalaReflectionException: expected a member of class Boolean, you provided method squid.lib.And
    }
    
    val c1 = ir{algo.joinLinesComplex(_:Iterable[String])}
    val r1 = algo.joinLinesComplex(ls)
    
    assert(r1 == res)
    assert((ls |> c1.run) == r1)
    
    Compiler.wrapOptim("JoinLinesComplexs") {
      val r = Compiler.optimize(c1)
      //println(ls |> r.run)  // FIXME: java.lang.NullPointerException
    }
    
  }
  test("FlatMap") {
    import Sequence._
    
    val ls = IndexedSeq[IndexedSeq[Char]]("lol","okay","test")
    
    /*
    //val c0 = ir{(xs:Iterable[Iterable[Char]]) => fromIterable(xs).flatMap(a => fromIterable(a)).fold(0)((ac,_) => ac + 1)}
    //val c0 = ir{(xs:IndexedSeq[IndexedSeq[Char]]) => fromIndexed(xs).flatMap(a => fromIndexed(a)).fold(0)((ac,_) => ac + 1)} // FIXME flatMap fusion does not kick in
    val c0 = ir{(xs:IndexedSeq[IndexedSeq[Char]]) => fromIndexed(xs).flatMap(a => fromIterable(a)).fold(123)((ac,_) => ac + 1)} // here it does
    val r0 = fromIndexed(ls).flatMap(a => fromIterable(a)).fold(123)((ac,_) => ac + 1)
    
    Compiler.wrapOptim("FlatMap") {
      val r = Compiler.optimize(c0)
      assert((ls |> r.run) == r0)
    }
    */
    
    
    val c1 = ir{ (xs: IndexedSeq[IndexedSeq[IndexedSeq[Int]]]) => 
      fromIndexed(xs).flatMap(a => fromIndexed(a).flatMap(b => fromIndexed(b))).fold(123)(_ + _)
    }
    
    Compiler.wrapOptim("FlatMapInFlatMap") {
      val r = Compiler.optimize(c1)
      //println(r.run.apply(IndexedSeq(IndexedSeq(IndexedSeq(1,2,3)))))
      println(r.compile.apply(IndexedSeq(IndexedSeq(IndexedSeq(1,2,3)))))
      //assert((ls |> r.run) == r0)
    }
    
    
    //val c2 = ir{ (xs: IndexedSeq[IndexedSeq[IndexedSeq[Int]]]) => 
    val c2 = ir{ (xs: IndexedSeq[IndexedSeq[Int]]) => 
      //fromIndexed(xs).flatMap(a => fromIndexed(a)).flatMap(b => fromIndexed(b)).fold(123)(_ + _)
      //fromIndexed(xs).flatMap(a => fromIndexed(a).map(fromIndexed)).flatMap(b => b).fold(123)(_ + _) // FIXME doesn't fuse
      fromIndexed(xs).map(fromIndexed).flatMap(b => b).fold(123)(_ + _) // FIXedME doesn't fuse
    }
    
    Compiler.wrapOptim("MapThenFlatMap") {
      val r = Compiler.optimize(c2)
      //println(r.run.apply(IndexedSeq(IndexedSeq(IndexedSeq(1,2,3)))))
      //println(r.compile.apply(IndexedSeq(IndexedSeq(IndexedSeq(1,2,3)))))
      println(r.compile.apply(IndexedSeq(IndexedSeq(1,2,3))))
      //assert((ls |> r.run) == r0)
    }
    
    
    val c3 = ir{ (xs: IndexedSeq[IndexedSeq[IndexedSeq[Int]]]) => 
      fromIndexed(xs).flatMap(a => fromIndexed(a).map(fromIndexed)).flatMap(b => b).fold(123)(_ + _) // FIXME doesn't fuse
    }
    
    Compiler.wrapOptim("FlatMapThenFlatMap") {
      val r = Compiler.optimize(c3)
      println(r.compile.apply(IndexedSeq(IndexedSeq(IndexedSeq(1,2,3)))))
      //assert((ls |> r.run) == r0)
    }
    
  }
  
  test("Zip") {
    import Sequence._
    
    val xs = IndexedSeq(1,2,3)
    //val ys = IndexedSeq('a, 'b, 'c, 'd)
    val ys = Seq('a, 'b, 'c, 'd)
    
    /*
    //val c0 = ir{(xs:IndexedSeq[Int],ys:IndexedSeq[Symbol]) => fromIndexed(xs)}
    val c0 = ir{(xs:IndexedSeq[Int],ys:Iterable[Symbol]) => 
      fromIndexed(xs).zip(fromIterable(ys).map(_.name)).fold("")((acc,xy) => acc + xy._1 + ":" + xy._2 + "; ")}
    //val r0 = fromIndexed(ls).flatMap(a => fromIterable(a)).fold(123)((ac,_) => ac + 1)
    
    Compiler.wrapOptim("ZipLinearLinear") {
      val r = Compiler.optimize(c0)
      println(r.run.apply(xs,ys))
      //assert(r.run.apply() == r0)
    }
    */
    
    val c1 = ir{(xs:IndexedSeq[Int],ys:Iterable[Int]) => 
      fromIndexed(xs).flatMap(x => fromIterable(ys).map(_ + x)).zip(fromIterable(ys)).fold("")((acc,xy) => acc + xy._1 + xy._2)}
    
    Compiler.wrapOptim("ZipFlatmapLinear") {
      val r = Compiler.optimize(c1) // FIXME flatmap fusion does not kick in
      //println(r)
      //println(r.run.apply(xs,xs)) // FIXME
      println(r.compile.apply(xs,xs))
      println(xs.flatMap(x => xs.map(_ + x)).zip(xs).foldLeft("")((acc,xy) => acc + xy._1 + xy._2))
      //assert(r.run.apply() == r0)
    }
    
  }
  
  /* // TODO test:
  
  zip(map(fromIndexed,f),map(fromIterable,g))  --> should use efficient linear-fused impl
  
  zip(nested,linear)
  zip(linear,nested)
  zip(zip(linear,linear),linear)
  
  try to encode unzip as sugar for two maps...
    but then we'll probably need horrizontal fusion -- possibly in the ImplFlowOptimizer
  
  */
  
  
  /* // TODO
  test("Avg Words") {
    
    val txt = "Hello there. This is a sentence. This is another, longer one."
    val res = 11.0/3
    
    val c0 = ir{algo.avgWordsPerSentence _}
    val r0 = algo.avgWordsPerSentence(txt)
    //println(r0)
    //println(c0)
    
    assert(r0 == res)
    assert((txt |> c0.run) == r0)
    
    Compiler.wrapOptim("AvgWords") {
      val r = Compiler.optimize(c0)
      //assert((txt |> r.run) == r0)
    }
    
  }
  */
  
  
  /*
  test("WAT") {
    
    val c0 = ir{algo.wat}
    println(c0)
    Compiler.wrapOptim("Wat") {
      val r = Compiler.optimize(c0)
    }
    
  }
  */
  
}

