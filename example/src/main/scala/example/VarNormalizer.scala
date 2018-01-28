// Copyright 2017 EPFL DATA Lab (data.epfl.ch)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package example

import squid._
import utils._
import ir._
import utils.Debug.show

trait VarNormalizer extends SimpleRuleBasedTransformer { self =>
  import base.Predef._
  import self.base.InspectableCodeOps
  import self.base.IntermediateCodeOps
  
  import squid.lib.MutVar
  
  rewrite {
  
    // Removal of Var[Unit]
    case code"var $v: Unit = (); $body: $t" => // Note that Unit <: AnyVal and cannot take value `null`
      //body subs 'v -> ir"()"  // No, wrong type! (Error:(22, 23) Cannot substitute free variable `v: squid.lib.Var[Unit]` with term of type `Unit`)
      //body rewrite { case code"$$v.!" => code"()" case code"$$v:=(())" => code"()" } subs 'v -> {throw RewriteAbort()}
      v.substitute[t.Typ, v.OuterCtx](body rewrite { case code"$$v.!" => code"()" case code"$$v:=(())" => code"()" }, throw RewriteAbort())
      
  }
      
}
