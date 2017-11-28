package squid
package anf

class TypeChangingTransfo extends MyFunSuite(SimpleANFTests.DSLWithEffects) {
  import DSL.Predef._
  import DSL.Quasicodes._
  import DSL.{ANFTypeChangingCodeTransformer}
  
  object Tr extends DSL.SelfTransformer with ANFTypeChangingCodeTransformer {
    override def transformChangingType[T,C](code: Code[T,C]): Code[_,C] = code match {
      case code"Symbol($str)" => str
      case code"println($x)" => code"println(${transformChangingType(x)})"
      case _ => super.transformChangingType(code)
    }
  }
  
  test("Basic") {
    
    code"println('ok)" transformWith Tr eqt code"""println("ok")"""
    
  }
  
  test("Lambdas") {
    
    code"(s:String) => Symbol(s)" transformWith Tr eqt code"(s:String) => s"
    
    // Note: omitting the `:Any` ascription here breaks the transformation, because the default recursive call that 
    // transforms the prefix to `.toString` sees the term changing type and gives up.
    code"(n:Int) => ('ok:Any).toString * n" transformWith Tr eqt 
      code"(n:Int) => augmentString(${ code""""ok"""":Code[Any,Any] }.toString) * n"
    // ^ this is a bit tricky: the `.toString` symbol in the transformed code is that of Ant, BUT the object to which it
    // is applied is "ok", which is known to be a 'pure' type and thus the whole thing is not let-bound...
    
  }
  
}
