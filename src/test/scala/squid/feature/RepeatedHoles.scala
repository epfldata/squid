package squid
package feature

class RepeatedHoles extends MyFunSuite {
  import TestDSL.Predef._
  
  val e = code"HPair(HPair(1,1), HPair(1,1)).second".erase
  
  test("Repeated Term Holes") {
    
    e match {
      case code"HPair[$tp]($p,p).second" =>
        eqt(tp.rep, typeRepOf[HPair[Int]])
        eqt(p, code"HPair(1,1)")
    }
    e match {
      case code"HPair[$tp](p,$p).second" =>
        eqt(tp.rep, typeRepOf[HPair[Int]])
        eqt(p, code"HPair(1,1)")
    }
  }
  
  test("Repeated Term and Type Holes") {
    
    e match {
      case code"HPair(HPair[$tn](n,n),HPair[tn]($n,n)).second" =>
        eqt(tn.rep, typeRepOf[Int])
        eqt(n, code"1")
    }
    e match {
      case code"HPair($a:$t, $_).second" =>
        eqt(t.rep, typeRepOf[HPair[Int]])
    }
    
  }
  
}

