package squid

import utils._
import Debug.show
import ir._

/** DSL Base that optimizes some List and Function1 operations like map and andThen. */
class OptimTestDSL extends SimpleAST with OnlineOptimizer with SimpleRuleBasedTransformer {
  import Predef._
  
  rewrite {
    //case ir"List[$t]($xs*).size" => ir"${Const(xs.size)}"
    
    /** To check that optimizations were applied */
    case code" 'unoptimized " => code" 'optimized "
      
    /** map map -> map */
    case code"($ls: List[$t0]) map ($f: t0 => $t1) map ($g: t1 => $t2)" =>
      code"$ls map ($f andThen $g)"
      
    /** lambda andThen -> lambda */
    case code"((p: $t0) => $body: $t1) andThen ($g: t1 => $t2)" =>
      code"(p: $t0) => $g($body)"
    
    /** andThen lambda -> lambda */
    case code"($f: $t0 => $t1) andThen ((p: t1) => $body: $t2)" =>
      code"(p2: $t0) => { val p = $f(p2); $body }"
      
    /** andThen andThen apply -> apply */
    case code"($f: $t0 => $t1) andThen ($g: t1 => $t2) apply $a" => code"$g($f($a))"
      
    /** lambda apply -> . */
    case code"((p: $t0) => $body: $t1)($arg)" => body subs ('p -> arg)
    // Version with intermediate binding (against code dup): -- may loop if val bindings are represented as redexes!!
    //case ir"((param: $t0) => $body: $t1)($arg)" => ir"val param = $arg; $body"
      
      
    /** list map -> list */
    case code"List[$t0]($xs*).map($f: t0 => $t1)" =>
    //case ir"List[$t0](${xs @ __*}).map($f: t0 => $t1)" => // FIXME: Error:(13, 11) exception during macro expansion: scala.MatchError: (xs @ (__* @ _)) (of class scala.reflect.internal.Trees$Bind)
      // FIXME $xs* syntax!
      
      // works:
      code"List(${ xs map (r => code"$f($r)"): _* })"
      
      // works:
      //val args = xs map (r => ir"$f($r)")
      //dbg_ir"List(${ args }*)"
      
      //dbg_ir"List(${ xs }*).asInstanceOf[List[$t1]]" // FIXME: Error:(46, 21) exception during macro expansion: java.lang.ClassNotFoundException: scala.Any 
      
    // Version with intermediate binding (against code dup):
    //case ir"List[$t0]($xs*).map($f: t0 => $t1)" =>
    //  ir"val f = $f; List(${ xs map (r => ir"($$f: ($t0 => $t1))($r)"): _* })"
    
    
    
    /** Notes: */
    //case ir"($f: $t0 => $t1) andThen ($g: t1 => $t2)" => ir"(x: $t0) => $g($f(x))"  // raises StackOverflow! (why?)
    
  }
  
}

