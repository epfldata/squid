package squid
package anf.transfo

import utils._
import ir._
import utils.Debug.show

/**
  * Created by lptk on 11/02/17.
  * 
  * Transforms option variables into a pair of variables (one boolean and oen containing the value if any).
  * This transformation will not successfully apply if the code is not normal w.r.t `OptionNormalizer`.
  * Also removes `Var[Unit]`, `Var[Tuple2[_]]` and some instances of `Var[Var[_]]`.
  * 
  */
trait VarFlattening extends SimpleRuleBasedTransformer { self =>
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  import squid.lib.Var
  import squid.lib.uncheckedNullValue
  
  rewrite {
    
    
    // Removal of Var[Unit]
    case code"var $v: Unit = (); $body: $t" => // Note that Unit <: AnyVal and cannot take value `null`
      //body subs 'v -> ir"()"  // No, wrong type! (Error:(22, 23) Cannot substitute free variable `v: squid.lib.Var[Unit]` with term of type `Unit`)
      body rewrite { case code"$$v.!" => code"()" case code"$$v:=(())" => code"()" } subs 'v -> Abort()
    
    
    // Removal of Var[Option[_]]
    case code"var $v: Option[$t] = $init; $body: $bt" =>
      val isDefined = code"isDefined? : Var[Bool]"
      val optVal = code"optVal? : Var[$t]"
      
      // Note: applying sub-rewritings sch as `case ir"$$v.!.isDefined" =>` is not going to work well, because it will
      // not rewrite cases such as `var a = Option(42); val v = a; (v.isDefined, v.isDefined)`...
      // Instead, we really need another level of usage-in-body rewriting for `ir"$$v.!"` bound values.
      
      //println(s"REM $v "+v.rep)
      
      val body2 = body rewrite {
        case code"val $x = $$v.! ; $sbody: $bt" =>
          val sbody2 = sbody rewrite {
            case code"$$x.isDefined" => code"$isDefined.!"
            case code"$$x.get" => 
              val r = code"$optVal.!" // TODO assert...?
              //println(s"R $r")
              r
          }
          //println("RW1 "+sbody)
          //println("RW2 "+sbody2)
          sbody2 subs 'x -> Abort()
        case code"$$v := None" => code"$isDefined := false"
          
        case code"$$v := Some($x:$$t)" => code"$optVal := $x; $isDefined := true"
        case code"val bound = Some($x:$$t); $$v := bound" => code"$optVal := $x; $isDefined := true"
        // FIXME: ^ this is a temporary kludge because the ANF matcher does not yet handle this with the pattern of the case above
          
        case code"$$v := $x" =>
          Abort() // TODO rewrite to if-then-else rebuilding the option -- note this may be tricky if options are not
          // normalized online, as it could lead to transforming `opt.isEmpty` into the ite before it is rewritten to
          // `!opt.isDefined` and handled properly by this transformer...
      }
      
      //println("RW "+body2)
      
      val body3 = body2 subs 'v -> Abort()
      //val body3 = body2 subs 'v -> {
      //  println(s"REMAINING 'v' IN $body2")
      //  Abort()}
      
      // FIXME make the `var` syntax work in:
      // TODOne use `uncheckableValue`
      //ir"""
      //  val isDefined = Var($init.isDefined)
      //  val optVal = Var($init getOrElse ${nullValue[t.Typ]})
      //  $body3
      //"""
      code"""
        val isDefined = Var($init.isDefined)
        val optVal = Var($init getOrElse uncheckedNullValue[$t])
        $body3
      """
      
      
    // Removal of Var[Tuple2[_]]
    case code"var $v: ($ta,$tb) = $init; $body: $bt" =>
      val lhs = code"lhs? : Var[$ta]"
      val rhs = code"rhs? : Var[$tb]"
      
      val body2 = body rewrite {
        case code"val $x = $$v.! ; $sbody: $bt" =>
          val sbody2 = sbody rewrite {
            case code"$$x._1" => code"$lhs.!"
            case code"$$x._2" => code"$rhs.!"
            //case ir"($$x:Any) == ($y:$t)" =>
              //ir"$lhs.! == $y._1 && "
          }
          sbody2 subs 'x -> Abort()
        case code"$$v := ($a:$$ta,$b:$$tb)" => code"$lhs := $a; $rhs := $b"
        case code"$$v := $x" => Abort() // TODO?
      }
      
      val body3 = body2 subs 'v -> Abort()
      
      if (init =~= code"uncheckedNullValue[($ta,$tb)]")
        code" val lhs = Var(uncheckedNullValue[$ta]);  val rhs = Var(uncheckedNullValue[$tb]);  $body3 "
      else
      code"""
        val lhs = Var($init._1)
        val rhs = Var($init._2)
        $body3
      """
      
      
    // Removal of Var[Var[_]] in some special cases
    case code"var $v: Var[$t] = $init; $body: $bt" =>
      val flatVar = code"flatVar? : Var[$t]"
      
      val body2 = body rewrite {
        case code"$$v.!.!" => code"$flatVar.!" // TODO genlze?
        case code"$$v := $x" => code"$flatVar := $x.!"
        case code"$$v.! := $x" => code"$flatVar := $x"
      }
      
      val body3 = body2 subs 'v -> Abort()
      //val body3 = body2 subs 'v -> {
      //  System.err.println(s"Variable v=$v still in $body2")
      //  Abort()}
      
      if (init =~= code"uncheckedNullValue[Var[$t]]")
        code"val flatVar = Var(uncheckedNullValue[$t]); $body3"
      else code"val flatVar = Var($init.!); $body3"
      
  }
      
}

