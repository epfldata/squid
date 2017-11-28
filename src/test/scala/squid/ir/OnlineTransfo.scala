package squid
package ir

import squid.utils.Debug

class OnlineTransfo extends MyFunSuite(OnlineTransfo.DSL) {
  import DSL.Predef._
  
  test("Constructed Terms are Rewritten") {
    
    eqt(code"2 + (readInt+1) + 3",
        code"6 + readInt")
    
    eqt(code"4 * ((readInt + 1) * 2 + 3)",
        code"20 + 8 * readInt")
    
    eqt(code"readInt * (readInt + 1)",
        code"readInt + readInt * readInt") // Note: that's why we need ANF
    
  }
  
  test("Extractor Terms are Rewritten") {
    
    code"4" match {
      case code"2 + 2" =>
    }
    
    code"1 + readInt" match {
      case code"readInt + 1" =>
    }
    
    code"6 + readInt" match {
      case code"2 + (($n:Int)+1) + 3" => eqt(n, code"readInt")
    }
    
  }
  
  test("Online Rewriting is Properly Recursive") {
    
    // Note: I verified that Scala does NOT P/E this, although it does things like '2+2'
    eqt(code"readInt + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1",
        code"10 + readInt")
    
  }
  
}
object OnlineTransfo {
  
  object DSL extends SimpleAST with OnlineOptimizer with SimpleRuleBasedTransformer {
    import Predef._
    
    transformExtractors = true
    
    rewrite { // Naive Addition/Multiplication Partial Evaluation
      
      // Addition P/E
      
      case code"0 + ($x: Int)" => x
        
      case code"(${Const(m)}: Int) + (${Const(n)}: Int)" => code"${Const(n + m)}"
        
      case code"($x: Int) + (${Const(n)}: Int)"             => code"${Const(n)} + $x"
      case code"($x: Int) + (($y: Int) + ($z: Int))"           => code"($x + $y) + $z"
        
        
      // Multiplication P/E
        
      case code"0 * ($x: Int)" => code"0"
      case code"1 * ($x: Int)" => x
        
      case code"(${Const(m)}: Int) * (${Const(n)}: Int)" => code"${Const(n * m)}"
        
      case code"($x: Int) * (${Const(n)}: Int)"             => code"${Const(n)} * $x"
      case code"($x: Int) * (($y: Int) * ($z: Int))"           => code"($x * $y) * $z"
      case code"($x: Int) * (($y: Int) + ($z: Int))"           => code"$x * $y + $x * $z" // Note: duplication of 'x'
      //case ir"($x: Int) * (($y: Int) + ($z: Int))"           => ir"val t = $x; t * $y + t * $z" // if not in ANF
      
    }
    /* // Note:
      case ir"0 + ($x: Int)" => ir"$x+($$y:Int)" // Error:(58, 34) Cannot rewrite a term of context [Unknown Context] to a stricter context [Unknown Context]{val y: Int}
    */
    
  }
}

