package squid
package feature

import squid.utils.meta.RuntimeUniverseHelpers
import utils.Debug._

class TypeMatching extends MyFunSuite {
  import TypeMatching._
  import TestDSL.Predef._
  
  test("Trivial") {
    code"42" matches {
      case code"$x: Any" => eqt(x, code"42")
    } and {
      case code"$x: AnyVal" => eqt(x, code"42")
    } and {
      case code"$x: $t" =>
        eqt(t.rep, base.constType(42))
        eqt(t.rep, x.trep)
        
        val opt = code"Option.empty[$t]"
        eqt(opt, code"Option.empty[Int]")
        
        // Note that opt.typ is `Option[Int(42)]`, so:
        assert(!(typeRepOf[Option[Int]] <:< opt.trep))
        subt(opt.trep, typeRepOf[Option[Int]])
    }
  }
  
  test("Matching Nothing Explicitly") {
    code"Seq()".erase match {
      //case ir"Seq()" => // should generate a warning
      case code"Seq[Nothing]()" => // should NOT generate a warning
    }
  }
  
  val f = code"(x: Int) => x.toDouble".erase
  
  test("Lambda Parameter/Body Types") {
    f matches {
      case code"(_: $xt) => $body: $bt" =>
        eqt(xt.rep, typeRepOf[Int])
        eqt(bt.rep, typeRepOf[Double])
        eqt(body.trep, typeRepOf[Double])
    } and {
      case code"(y: Nothing) => $body: Double" =>
        assert(!(body =~= code"(${base.`internal Code`(base.hole("y", typeRepOf[Nothing]))}: Int).toDouble"))
        eqt(body, code"${base.`internal Code`[Int,{}](base.hole("y", typeRepOf[Int]))}.toDouble")
        eqt(body, code"($$y: Int).toDouble")
        
        // Note: `body` has type `IR[Double,{val y: Nothing}]` but internally has a hole typed `Int`.
        // This is okay and sound, as the following shows:
        code"($$y:Int).toDouble" : Code[Double,{val y: Nothing}]
        
        assertDoesNotCompile(""" code"val y = 42; $body".run """) // Error:(48, 9) Embedding Error: Captured variable `y: Int` has incompatible type with free variable `y: Nothing` found in inserted IR $(body)
    }
  }
  
  test("Function Types") {
    f match {
      case code"$_: (Double => Double)" => fail
      case code"$_: ($a => $b)" =>
        assert(a.rep =:= typeRepOf[Int])
        assert(b.rep =:= typeRepOf[Double])
    }
    f match {
      case code"$_: (Int => $b)" =>
        assert(b.rep =:= typeRepOf[Double])
    }
    f match {
      case code"$_: ($a => Double)" =>
        assert(a.rep =:= typeRepOf[Int])
    }
    f match {
      case code"$_: (Any => Double)" => fail
      case code"$_: (AnyVal => Double)" => fail
      case code"$_: (Int => Any)" =>
      case code"$_: (Int => AnyVal)" => fail
    }
    
    code"Some[Int=>Int](_+1)" matches {
      case code"Some($f: ($ta => $tb))" =>
        //println(ta,tb)
        eqt(ta.rep, typeRepOf[Int])
        eqt(tb.rep, typeRepOf[Int])
    }
    code"((x:Int)=>x+1,(x:Int)=>x-1)" matches {
      case code"($_: ($ta => $tb), $_: (ta => tb))" => eqt(ta.rep,tb.rep)
    } and {
      case code"($_: ($ta => tb), $_: (ta => $tb))" => eqt(ta.rep,tb.rep)
    }
  }
  
  test("Extracting from Nothing") (
    
    code"Option.empty" matches {
      case code"$y: Option[Int]" =>
    } and {
      case code"$y: Option[$t]" => assert(t.rep =:= typeRepOf[Nothing])
    } and {
      case code"$y: Option[Option[$t]]" => assert(t.rep =:= typeRepOf[Nothing])
    }
    and { case code"Option.empty[$t]" => eqt(t.rep, typeRepOf[Nothing]) }
    and { case code"Option.empty[Any]" => } // cf: covariant method type argument matching
    and { case code"Option.empty[AnyVal]" => }
    and { case code"Option.empty[Nothing]" => }
    
  )
  
  
  test("Type Params & Variance") {
    
    code"List(42)" matches ({
      case code"$x: List[Any]" => eqt(x, code"List(42)")
    }, {
      case code"$x: List[AnyVal]" =>
    }, {
      case code"$_: List[$t]" => eqt(t.rep, typeRepOf[Int])
    })
    
    code"List(List(42))" matches ({
      case code"$_: List[List[$t]]" => eqt(t.rep, typeRepOf[Int])
    }, {
      case code"$_: Seq[Seq[Any]]" =>
    }, {
      case code"$_: Seq[Seq[AnyVal]]" =>
    })
    
    // TODO: test functions, contravariance and invariance...
    
  }
  
  
  val AnyType = codeTypeOf[Any]
  
  
  // Note: defining 'Expr' and 'Appl' here used to work; no more since symbols are now loaded dynamically from the owner chain
  
  test("GADT") {
    //lang.ScalaTyping.debugTypes(
    
    val applid = code"Appl[Int,Double]".erase
    applid match {
      case code"$a: Appl[$s,$t]" =>
        assert(s.rep =:= typeRepOf[Int])
        assert(t.rep =:= typeRepOf[Double])
      //case _ => fail
    }
    applid match {
      case code"$a: Appl[Any,Any]" =>
        assert(a =~= applid)
      //case _ => fail
    }
    applid match {
      case code"$a: Expr[$t]" =>
        assert(t.rep =:= typeRepOf[Double])
    }
    
    val abstis = code"Abst[Int,String]".erase
    abstis match { case code"$_ : Expr[Int => String]" => }
    abstis match { case code"$_ : Expr[Nothing => Any]" => }
    abstis match { case code"$_ : Expr[Any]" => }
    
    val abstabst = code"Abst[Abst[Int,String], Abst[Int,String]]".erase
    abstabst match {
      case code"$_ : Expr[Abst[Int,String] => Abst[Int,String]]" =>
    }
    abstabst match {
      case code"$_ : Expr[Abst[Int, String] => Expr[Int => String]]" =>
    }
    abstabst match {
      case code"$_ : Expr[Abst[Any, Nothing] => Expr[Nothing => Any]]" =>
    }
    
    code"(x: Appl[Int,Double]) => ()".cast[_ => Unit] match {
      case code"$_: (Appl[Int,Double] => Unit)" =>
    }
    
    code"(x: Appl[Int,Int]) => Int".cast[_ => _] match {
      case code"$_: (Appl[Int,Nothing] => Any)" =>
    }
    
    code"(x: Appl[Int,Double]) => Appl[Double,Int]".cast[_ => _] match {
      case code"$_: (Expr[$t1] => $t2)" => fail
      case code"$_: (Appl[$a,$b] => Expr[$t])" =>
        assert(a.rep =:= typeRepOf[Int])
        assert(b.rep =:= typeRepOf[Double])
        assert(t.rep =:= typeRepOf[Int])
    }
    
    code"(x: Expr[Int]) => ()".cast[_ => _] match {
      case code"$_: (Appl[String,Int] => Any)" =>
    }
    
    code"(x: Expr[Int]) => ()".cast[_ => _] match {
      case code"$_: (Appl[String,$t] => Unit)" =>
        eqt(t.rep, typeRepOf[Int])
    }
    
    code"(x: Expr[Int]) => ()".cast[_ => _] match {
      case code"$_: (Appl[$t,Int] => Unit)" =>
        eqt(t, AnyType)
    }
    
  }
  
  
  test("Extracted Type Variance & Unification") {
    
    val a = code"HPair(List(1,2,3),List('a','b'))"
    eqt(a, code"HPair[List[AnyVal]](List(1,2,3),List('a','b'))")
    
    a matches {
      case code"HPair[$t]($a,$b)" => eqt(t, codeTypeOf[List[AnyVal]])
    } and {
      case code"HPair($a:$ta,$b)" => // What happens: the pattern is typed:  ir"HPair[ta]($a:$ta,$b)"  so 'ta' is also matched against b, thence is unified to +List[AnyVal]
        assert(!(ta =:= codeTypeOf[List[Int]]))
        eqt(ta, codeTypeOf[List[AnyVal]])
    }
    
    assertDoesNotCompile(""" a match { case code"HPair($a:$ta,$b:$tb)" => } """) // Error:(197, 12) Embedding Error: Precise extracted type was lost, possibly because extruded from defining scope, in: <extruded type>
    
    
    val f = code"(x: List[Any]) => x.asInstanceOf[List[Int]]" : Code[List[Any] => List[Int], {}]
    
    f matches {
      case code"$g: ($t => t)" => // Our matcher can assign to 't' anything between 'List[Int]' and 'List[Any]'. Currently, it arbitrarily picks the lower bound.
        eqt(t, codeTypeOf[List[Int]])
    } and {
      case code"(_: $t) => $b: t" =>
        eqt(t, codeTypeOf[List[Int]])
    } and {
      case code"$g: ($t0 => $t1)" =>
        eqt(t0, codeTypeOf[List[Any]])
        eqt(t1, codeTypeOf[List[Int]])
    } and {
      case code"$_: (List[List[$t0]] => Any)" =>
        //show(t0)
        subt(t0, AnyType)
        subt(codeTypeOf[Nothing], t0)
    }
    
    // FIXME: use interval types
    //ir"($f,42)" matches { // Could not merge types =Int(42) and =Int
    //  case ir"($_: (List[List[$t0]] => Any), $_: t0)" =>
    //    eqt(t0, irTypeOf[Int])
    //}
    
    code"(x: Any) => 'ok" matches {
      case code"$_: ((List[$t0] => Int) => t0)" =>
        eqt(t0, codeTypeOf[Symbol])
    } and {
      case code"$_: ((List[$t0] => Int) => Symbol)" =>
        eqt(t0, AnyType)
    } and {
      case code"$_: (($t0 => Int) => Symbol)" =>
        eqt(t0, AnyType)
    } and {
      case code"$_: (($t0 => Int) => t0)" =>
        eqt(t0, codeTypeOf[Symbol])
    }
    
  }
  
  
  test("Bounds") {
    
    val q: Code[Any,Any] = code"foo[List[Int]]"
    val t = q match {
      case code"foo[$s where (s <:< Seq[Int])]" =>
        s
    }
    eqt(t, codeTypeOf[List[Int]])
    
    code"Some(Nil).orElse(Some(List(0)))" matches {
      case code"($lhs:Option[$t]).orElse($rhs:Option[t])" => eqt(t, codeTypeOf[List[Int]])
    } and {
      case code"($lhs:Option[$ta]).orElse($rhs:Option[$tb where (ta <:< tb)])" =>
        eqt(ta, codeTypeOf[Nil.type])
        eqt(tb, codeTypeOf[List[Int]])
    } and {
      case code"($lhs:Option[$ta where (ta <:< tb)]).orElse($rhs:Option[$tb])" =>  // even works when we forward-refer to `tb`!
        eqt(ta, codeTypeOf[Nil.type])
        eqt(tb, codeTypeOf[List[Int]])
    }
    
    code"bar[Int,String,Abst[Int,AnyRef]]" matches {
      case code"bar[$a, $b, $t where (Abst[a,b] <:< t <:< Expr[Any])]" =>
        eqt(a, codeTypeOf[Int])
        eqt(b, codeTypeOf[String])
        eqt(t, codeTypeOf[Abst[Int,AnyRef]]) // Q: why does it show as Abst[Int,Any]?
        //eqt(t, irTypeOf[Abst[Int,Any]])    // Q: and even compares equal to it?!
    }
    
  }
  
  test("Bounds Checking") {
    
    // cf. https://github.com/LPTK/Squid/issues/15
    
    code"List(0)" matches {
      case code"$ls:List[$t where (t <:< String)]" => // fail // FIXME
      case code"$ls:List[$t where (t <:< AnyVal)]" => eqt(t, codeTypeOf[Int])
    }
    
  }
  
}

object TypeMatching {
  class Expr[+A]
  class Abst[-A,+B] extends Expr[A => B]
  object Abst { def apply[A,B] = new Abst[A,B] }
  class Appl[+A,+B] extends Expr[B]
  object Appl { def apply[A,B] = new Appl[A,B] }
  
  def foo[T <: Seq[Int]] = ()
  def bar[A,B,T >: Abst[A,B] <: Expr[Any]] = ()
}


