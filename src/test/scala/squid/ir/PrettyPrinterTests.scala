package squid
package ir

import org.scalatest.FunSuite
import MacroTesters._

class PrettyPrinterTests extends FunSuite {
  object b extends ir.SimpleAST
  
  val Inter = new ir.PrettyPrinter
  
  def same[A](xy: (A, A)) = assert(xy._1 == xy._2)
  def runSame[A](xy: (b.Rep, A), exp: String) = {
    same((b.reinterpret(xy._1, Inter)())(0), exp)
  }
  
  test("Constants") ({
    
    runSame( shallowAndDeep(b){ 42 }, "42" )
    
    runSame( shallowAndDeep(b){ "ok" }, """"ok"""" )
    
    runSame( shallowAndDeep(b){ 'c' }, "'c'" )
    
    runSame( shallowAndDeep(b){ 'Cool }, "'Cool" )
    
  })
  
  test("Basic") {{

    val act0 = shallowAndDeep(b){ "ok".reverse }
    val exp0 =
      """
        |scala.Predef.augmentString("ok").reverse
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ "ok".take(1)+"ko" }
    val exp1 =
      """
        |scala.Predef.augmentString("ok").take(1).+("ko")
      """.stripMargin.trim

    val act2 = shallowAndDeep(b){ {0 -> 1} swap }
    val exp2 =
      """
        |scala.Predef.ArrowAssoc[scala.Int](0).->[scala.Int](1).swap
      """.stripMargin.trim

    val act3 = shallowAndDeep(b){ Array.ofDim[Float](10) }
    val exp3 =
      """
        |scala.Array.ofDim[scala.Float](10)(scala.reflect.ClassTag.Float)
      """.stripMargin.trim

    val act4 = shallowAndDeep(b){ new scala.Array[Int](10)}
    val exp4 =
      """
        |new scala.Array[scala.Int](10)
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
    runSame(act2, exp2)
    runSame(act3, exp3)
    runSame(act4, exp4)
  }}

  test("Bindings") {

    //runSame( shallowAndDeep(b){ (arg: {val y:Int}) => arg.y } )  // Unsupported feature: Refinement type 'AnyRef{val y: Int}'

    val act0 = shallowAndDeep(b){ val x = 0; x + 1 }
    val exp0 =
      """
        |val x: scala.Int = 0
        |x.+(1)
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ ((x: Int) => x + 1)(42) }
    val exp1 =
      """
        |val x: scala.Int = 42
        |x.+(1)
      """.stripMargin.trim

    val act2 = shallowAndDeep(b){ {x: Int => x + 1}.apply(42) }
    val exp2 =
      """
        |val x: scala.Int = 42
        |x.+(1)
      """.stripMargin.trim

    val act3 = shallowAndDeep(b){ val f = (x: Int) => x + 1}
    val exp3 =
      """
        |val f: scala.Function1[scala.Int, scala.Int] = ((x: scala.Int) => x.+(1))
        |()
      """.stripMargin.trim

    val act4 = shallowAndDeep(b){ val f = (x: Int) => x + 1; f(42)}
    val exp4 =
      """
        |val f: scala.Function1[scala.Int, scala.Int] = ((x: scala.Int) => x.+(1))
        |f(42)
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
    runSame(act2, exp2)
    runSame(act3, exp3)
    runSame(act4, exp4)
  }

  test("Variables") {

    val act0 = shallowAndDeep(b){ lib.Var(0) }
    val exp0 =
      """
        |0
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ var x = ("ok" + "ko".reverse).length; x-=1; (x+=1, x, 'lol) }
    val exp1 =
      """
        |var x: scala.Int = "ok".+(scala.Predef.augmentString("ko").reverse).length()
        |x = x.-(1)
        |(x = x.+(1), x, 'lol)
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
  }

  test("By-name") {{

    val act0 = shallowAndDeep(b){ Dummies.byNameMethod(42) }
    val exp0 =
      """
        |squid.Dummies.byNameMethod(42)
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ Dummies.byNameMethod(666) }
    val exp1 =
      """
        |squid.Dummies.byNameMethod(666)
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
  }}

  test("Varargs") {

    val act0 = shallowAndDeep(b){ lib.Imperative()(42) }
    val exp0 =
      """
        |42
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ var x = 0; lib.Imperative(x += 1)(x) }
    val exp1 =
      """
        |var x: scala.Int = 0
        |x = x.+(1)
        |x
      """.stripMargin.trim

    val act2 = shallowAndDeep(b){ var x = 0; lib.Imperative(x += 1, x += 1)(x) }
    val exp2 =
      """
        |var x: scala.Int = 0
        |x = x.+(1)
        |x = x.+(1)
        |x
      """.stripMargin.trim

    val act3 = shallowAndDeep(b){ var x = 0; val modifs = Seq(x += 1, x += 1); lib.Imperative(modifs: _*)(x) }
    val exp3 =
      """
        |var x: scala.Int = 0
        |val modifs: scala.collection.Seq[scala.Unit] = scala.collection.Seq[scala.Unit](x = x.+(1), x = x.+(1))
        |modifs
        |x
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
    runSame(act2, exp2)
    runSame(act3, exp3)
  }

  test("Virtualized Constructs") {

    // Ascription
    val act0 = shallowAndDeep(b){ (List(1,2,3) : Seq[Any]).size: Int }
    val exp0 =
      """
        |(scala.collection.immutable.List[scala.Int](1, 2, 3): scala.collection.Seq[scala.Any]).size
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ "ok".length: Unit }
    val exp1 =
      """
        |"ok".length()
        |()
      """.stripMargin.trim

    // If then else
    val act2 = shallowAndDeep(b){ if (Math.PI > 0) "ok" else "ko" }
    val exp2 =
      """
        |if (true) { "ok" } else { "ko" }
      """.stripMargin.trim

    val act3 = shallowAndDeep(b){ var x = 0; if (true) x += 1 else x += 1; x }
    val exp3 =
      """
        |var x: scala.Int = 0
        |if (true) { x = x.+(1) } else { x = x.+(1) }
        |x
      """.stripMargin.trim

    // While
    val act4 = shallowAndDeep(b){ var x = 0; while (x < 3) { x += 1; println(x) }; x }
    val exp4 =
      """
        |var x: scala.Int = 0
        |while (x.<(3)) {
        |  x = x.+(1)
        |  scala.Predef.println(x)
        |}
        |x
      """.stripMargin.trim

    val act5 = shallowAndDeep(b){ var x = if (true) 5 else 6; x }
    val exp5 =
      """
        |var x: scala.Int = if (true) { 5 } else { 6 }
        |x
      """.stripMargin.trim

    val act6 = shallowAndDeep(b){ var x = 5; if (5 * x > 0) x += 1; x}
    val exp6 =
      s"""
         |var x: scala.Int = 5
         |if (5.*(x).>(0)) { x = x.+(1) }
         |x
       """.stripMargin.trim

    val act7 = shallowAndDeep(b){ var x = Math.random(); if (x > 0) { println("greater!"); x = 0 } else { println("smaller!"); x = 1 }; x }
    val exp7 =
      """
        |var x: scala.Double = java.lang.Math.random()
        |if (x.>(0)) {
        |  scala.Predef.println("greater!")
        |  x = 0.0
        |} else {
        |  scala.Predef.println("smaller!")
        |  x = 1.0
        |}
        |x
      """.stripMargin.trim

    val act8 = shallowAndDeep(b) { var i = 0; var y = 100; while (i < 3) { if (y % 10 == 0) { y /= 10; y * y }; i += 1}; y}
    val exp8 =
      """
        |var i: scala.Int = 0
        |var y: scala.Int = 100
        |while (i.<(3)) {
        |  if (y.%(10).==(0)) {
        |    y = y./(10)
        |    y.*(y)
        |  }
        |  i = i.+(1)
        |}
        |y
      """.stripMargin.trim

    val act9 = shallowAndDeep(b) {
      val A = Array(Array(1, 2, 3), Array(1, 2, 3), Array(1, 2, 3))
      var i = 0; var j = 0
      while (i < 3) {
        while (j < 3) {
          A(i)(j) = i * j
          j += 1
        }
        i += 1
      }
      A
    }
    val exp9 =
      """
        |val A: scala.Array[scala.Array[scala.Int]] = scala.Array[scala.Array[scala.Int]](scala.Array(1, 2, 3), scala.Array(1, 2, 3), scala.Array(1, 2, 3))(scala.reflect.ClassTag[scala.Array[scala.Int]](scala.runtime.ScalaRunTime.arrayClass(int)))
        |var i: scala.Int = 0
        |var j: scala.Int = 0
        |while (i.<(3)) {
        |  while (j.<(3)) {
        |    A(i).update(j, i.*(j))
        |    j = j.+(1)
        |  }
        |  i = i.+(1)
        |}
        |A
      """.stripMargin.trim

    val act10 = shallowAndDeep(b) {
      var x = 5
      if (5 * x > 0) {
        x += 1
        if (true) x += 1
        else {
          println(x)
          println(x)
        }
      }
      x
    }
    val exp10 =
      """
        |var x: scala.Int = 5
        |if (5.*(x).>(0)) {
        |  x = x.+(1)
        |  if (true) { x = x.+(1) }
        |  else {
        |    scala.Predef.println(x)
        |    scala.Predef.println(x)
        |  }
        |}
        |x
      """.stripMargin.trim

    val act11 = shallowAndDeep(b) {
      var x = 5
      if (5 * x > 0) {
        x += 1
        if (true) {
          x += 1
          println(x)
        }
        else {
          println(x)
          println(x)
        }
      }
      x
    }
    val exp11 =
      """
        |var x: scala.Int = 5
        |if (5.*(x).>(0)) {
        |  x = x.+(1)
        |  if (true) {
        |    x = x.+(1)
        |    scala.Predef.println(x)
        |  } else {
        |    scala.Predef.println(x)
        |    scala.Predef.println(x)
        |  }
        |}
        |x
      """.stripMargin.trim

    val act12 = shallowAndDeep(b) {
      var x = 5
      if (5 * x > 0) {
        x += 1
        if (true) {
          x += 1
          println(x)
        }
        else { println(x) }
      }
      x
    }
    val exp12 =
      """
        |var x: scala.Int = 5
        |if (5.*(x).>(0)) {
        |  x = x.+(1)
        |  if (true) {
        |    x = x.+(1)
        |    scala.Predef.println(x)
        |  } else { scala.Predef.println(x) }
        |}
        |x
      """.stripMargin.trim

    val act13 = shallowAndDeep(b){ var x = 10; while (x > 0) { x = x - 1 }; x }
    val exp13 =
      """
        |var x: scala.Int = 10
        |while (x.>(0)) { x = x.-(1) }
        |x
      """.stripMargin.trim

    val act14 = shallowAndDeep(b){
      var x = 10
      while (x > 0) {
        var y = 10
        while (y > 0) { y = y - 1 }
        x = x - 1
      }
      x
    }
    val exp14 =
      """
        |var x: scala.Int = 10
        |while (x.>(0)) {
        |  var y: scala.Int = 10
        |  while (y.>(0)) { y = y.-(1) }
        |  x = x.-(1)
        |}
        |x
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
    runSame(act2, exp2)
    runSame(act3, exp3)
    runSame(act4, exp4)
    runSame(act5, exp5)
    runSame(act6, exp6)
    runSame(act7, exp7)
    runSame(act8, exp8)
    runSame(act9, exp9)
    runSame(act10, exp10)
    runSame(act11, exp11)
    runSame(act12, exp12)
    runSame(act13, exp13)
    runSame(act14, exp14)
  }

  test("Java") {{

    // overloading
    val act0 = shallowAndDeep(b){ "ok".indexOf('k'.toInt) }
    val exp0 =
      """
        |"ok".indexOf('k'.toInt)
      """.stripMargin.trim

    val act1 = shallowAndDeep(b){ "ok".indexOf('k') }
    val exp1 =
      """
        |"ok".indexOf(107)
      """.stripMargin.trim

    val act2 = shallowAndDeep(b){ "okok".indexOf("ok") }
    val exp2 =
      """
        |"okok".indexOf("ok")
      """.stripMargin.trim

    val act3 = shallowAndDeep(b){ "okok".lastIndexOf("ok") }
    val exp3 =
      """
        |"okok".lastIndexOf("ok")
      """.stripMargin.trim

    val act4 = shallowAndDeep(b){ String.valueOf(true) }
    val exp4 =
      """
        |java.lang.String.valueOf(true)
      """.stripMargin.trim

    val act5 = shallowAndDeep(b){ "ok"+String.valueOf("ko") }
    val exp5 =
      """
        |"ok".+(java.lang.String.valueOf("ko"))
      """.stripMargin.trim

    val act6 = shallowAndDeep(b){ ("ko" * 2) }
    val exp6 =
      """
        |scala.Predef.augmentString("ko").*(2)
      """.stripMargin.trim

    val act7 = shallowAndDeep(b){ ("ok" + "ko"*2).length }
    val exp7 =
      """
        |"ok".+(scala.Predef.augmentString("ko").*(2)).length()
      """.stripMargin.trim

    runSame(act0, exp0)
    runSame(act1, exp1)
    runSame(act2, exp2)
    runSame(act3, exp3)
    runSame(act4, exp4)
    runSame(act5, exp5)
    runSame(act6, exp6)
    runSame(act7, exp7)
  }}
}














