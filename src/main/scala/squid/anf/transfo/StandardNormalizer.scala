package squid
package anf.transfo

import utils._
import ir._
import lang.{ScalaCore,InspectableBase}
import utils.Debug.show


trait StandardNormalizer extends SimpleRuleBasedTransformer 
  with CurryEncoding.ApplicationNormalizer 
  with OptionNormalizer 
  with TupleNormalizer
  with FunctionNormalizer
  with IdiomsNormalizer


/**
  * Created by lptk on 11/02/17.
  * 
  * Goal: reduce all Option operations to Some, None, isDefined and get, so as to simplify further passes.
  * 
  * TODO for Either
  * TODO generalize, for all ADTs? (reinterpret all ADTs as Either's?)
  * 
  */
trait OptionNormalizer extends SimpleRuleBasedTransformer { self =>
  val base: InspectableBase with ScalaCore
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
   // To generate on cases statically-known to be failures;
   // will help remove dead code under the assumption this is an undefiend behavior:
  lazy val NoneGet = code"""assert(false, "None.get").asInstanceOf[Nothing]"""
  
  rewrite {
      
    // Simplifications
    
    case code"Some[$t]($v).get" => code"$v"
    case code"None.get" => NoneGet
    case code"Some[$t]($v).getOrElse($d)" => code"$v"
    case code"None.getOrElse[$t]($d)" => code"$d"
    //case ir"Some[$t]($_).isDefined" => ir"true" // FIXME allow `_` in patterns...
    case code"Some[$t]($v).isDefined" => code"true"
    case code"None.isDefined" => code"false"
      
    // Methods `isEmpty` and `get` are redefined in `Some` and `None` (ie Some.get is not the same symbol as Option.get),
    // so we need to handle the separate Option symbols here:
    case code"(Some[$t]($v):Option[t]).isEmpty" => code"false"
    case code"(Some[$t]($v):Option[t]).get" => code"$v"
    case code"(None:Option[$t]).isEmpty" => code"true"
    case code"(None:Option[$t]).get" => NoneGet
      
      
    // Feature Streamlining
    
    case code"Option.empty[$t]" => code"None"
    case code"Option[$t]($v)" => code"if ($v == null) None else Some($v)"
    case code"($opt:Option[$t]).nonEmpty" => code"$opt.isDefined"
    case code"($opt:Option[$t]).isEmpty" => code"!$opt.isDefined"
    case code"($opt:Option[$t]).fold[$s]($dflt)($thn)" => code"if ($opt.isDefined) $thn($opt.get) else $dflt"
    case code"($opt:Option[$t]).filter($f)" => code"if ($opt.isDefined && $f($opt.get)) $opt else None"
    case code"($opt:Option[$t]).map[$mt]($f)" => code"if ($opt.isDefined) Some($f($opt.get)) else None"
    case code"($opt:Option[$t]).flatMap[$mt]($f)" => code"if ($opt.isDefined) $f($opt.get) else None"
    case code"($opt:Option[$t]).orElse[t]($other)" => code"if ($opt.isDefined) $opt else $other" // TODO test with different type params
    case code"($opt:Option[$t]).foreach[$r]($f)" => code"if ($opt.isDefined) {$f($opt.get);()} else ()"
    // TODO handle other features...
    
    // Commuting with IF
    
    case code"(if ($c) $th else $el : Option[$t]).get" => code"if ($c) $th.get else $el.get"
    case code"(if ($c) $th else $el : Option[$t]).getOrElse($d)" => code"if ($c) $th.getOrElse($d) else $el.getOrElse($d)"
    case code"(if ($c) $th else $el : Option[$t]).isDefined" => code"if ($c) $th.isDefined else $el.isDefined"
    
  }
  
}

trait TupleNormalizer extends SimpleRuleBasedTransformer { self =>
  val base: InspectableBase with ScalaCore
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  rewrite {
      
    case code"($a:$ta) -> ($b:$tb)" => code"($a,$b)"
    case code"($a:$ta,$b:$tb)._1" => code"$a"
    case code"($a:$ta,$b:$tb)._2" => code"$b"
    case code"($a:$ta,$b:$tb).swap" => code"($b,$a)"
    case code"($a:$ta,$b:$tb).copy($va:$tc,$vb:$td)" => code"($va,$vb)"
      
  }
  
}

trait FunctionNormalizer extends SimpleRuleBasedTransformer { self =>
  val base: InspectableBase with ScalaCore
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  rewrite {
      
    case code"($f:$ta=>$tb).andThen[$tc]($g)" => code"(x:$ta) => $g($f(x))"
      
  }
  
}

trait IdiomsNormalizer extends SimpleRuleBasedTransformer { self =>
  val base: InspectableBase with ScalaCore
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  rewrite {
      
    case code"($str:String).toString" => code"$str"
      
    case code"($x:$t).asInstanceOf[t]" => code"$x:$t"
      
    case code"identity[$t]($x)" => x
      
  }
  
}

