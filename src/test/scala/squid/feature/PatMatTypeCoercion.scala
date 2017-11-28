package squid
package feature

import squid.utils.meta.RuntimeUniverseHelpers
import utils.Debug._

//class PatMatTypeCoercion extends MyFunSuite(anf.SimpleANFTests.DSL) {  // <-- already does beta reduction
class PatMatTypeCoercion extends MyFunSuite {
  import DSL.Predef.{Code=>CCode,_}
  //import DSL.{LeafCode}
  type Code[T] = DSL.Predef.Code[T,Any]
  
  test("Simple Type Coercion") {
    
    import quasi.SuppressWarning.`scrutinee type mismatch`
    
    // TODO: a way to remove the warning... without actually throwing the type info (which is being used)
    def foo[T:CodeType](x : CCode[List[T],Any]) = x match {
      case code"List[$t0]($x)" => code"$x:T" // compiles
    }
    
    assertDoesNotCompile("""
    def foo[T:CodeType](x : CCode[List[T],Any]) = x.erase match {  // erasure prevents subtyping knowledge to be obtained
      case code"List[$t0]($x)" => code"$x:T"
    }
    """)
    
    eqt(foo(code"List(1)").typ, codeTypeOf[Int])
    
  }
  
  test("GADT-like Pattern Matching") {
    
    def beta[T:CodeType](x:Code[T]): Code[T] = x match {
      case code"((p: $t0) => $body: T)($a: t0)" => body subs ('p -> beta(a))
      case code"($f: ($t0 => T))($a)" => val (f0, a0) = (beta(f), beta(a)); code"$f($a)":Code[T]
      case code"(p: $t0) => $body: $t1" =>
        val bodyf = (x:Code[t0.Typ]) => body subs 'p -> x
        code"{(p: $t0) => ${(x:Code[t0.Typ]) => beta(bodyf(x))}(p)} : T" // coercion
      case code"($a:Int) + ($b:Int)" => code"${beta(a)} + ${beta(b)} : T" // coercion
      
      //case LeafCode(_) => x
        
      case Const(n) => Const(n)
      case base.Code((base.RepDef(h:base.Hole))) => base.Code((base.rep(h)))
      case base.Code((base.RepDef(bv:base.BoundVal))) => base.Code((base.rep(bv)))
      // ^ Should use LeafCode, but LeafCode is currently only defined for SimpleANF
    }
    
    assertCompiles("""
      def foo[T:CodeType](x:Code[T]): Code[T] = x match {
        case code"$x:$t2" => code"$x:T" // compiles, good
        case code"$x:Int" => code"$x:T" // compiles, good
      }
    """)
    
    assertDoesNotCompile("""
      def foo[T:CodeType](x:Code[T]): Code[T] = x match {
        case code"println($x:$t2)" => code"$x:T" // rejected (good) -- t2 is a different type
      }
    """)
      
    assertDoesNotCompile("""
      def foo[T:CodeType](x:Code[T]): Code[T] = x match {
        case code"$x:Int" => code"$x:T"
        case code"println($x:Int)" => code"$x:T" // should reject; assumption in previous case (Int<:T) should not bleed through here!
      }
    """)
    
    code"((x:Int) => (y:Int) => x+y)(42)"        neqt code"(z:Int) => 42 + z"
    code"((x:Int) => (y:Int) => x+y)(42)" |> beta eqt code"(z:Int) => 42 + z"
    
  }
  
}