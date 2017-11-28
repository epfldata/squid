package example.doc

import squid.utils._
import squid.ir.{SimpleANF, BottomUpTransformer, StandardEffects}
import squid.lang.Optimizer
import squid.quasi.{phase, embed}

@embed object Test { @phase('MyPhase) def foo[T](xs: List[T]) = xs.head }

object IntroExample extends App {
  
  object Embedding extends SimpleANF with StandardEffects {
    embed(Test)
  }
  import Embedding.Predef._
  import Embedding.Quasicodes._
  import Embedding.Lowering
  
  val pgrm0 = code"(Test.foo(1 :: 2 :: 3 :: Nil) + 1).toDouble"
  println(pgrm0)
  val pgrm1 = pgrm0 transformWith (new Lowering('MyPhase) with BottomUpTransformer)
  println(pgrm1)
  val pgrm2 = pgrm1 fix_rewrite {
    case code"($xs:List[$t]).::($x).head" => x
    case code"(${Const(n)}:Int) + (${Const(m)}:Int)" => Const(n+m)
  }
  println(pgrm2)
  println(pgrm2.compile)
  
  
  // Making a dedicated static optimizer –– see the usage example in test file `IntroExampleTest`:
  
  class TestOptimizer extends Embedding.SelfCodeTransformer {
    def transform[T,C](pgrm0: Code[T,C]): Code[T,C] = {
      // same transformation as above:
      val pgrm1 = pgrm0 transformWith (new Lowering('MyPhase) with BottomUpTransformer)
      val pgrm2 = pgrm1 fix_rewrite {
        case code"($xs:List[$t]).::($x).head" => x
        case code"(${Const(n)}:Int) + (${Const(m)}:Int)" => Const(n+m)
      }
      pgrm2
    }
  }
  
}
