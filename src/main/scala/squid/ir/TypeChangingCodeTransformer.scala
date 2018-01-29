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

package squid
package ir

import utils._

trait TypeChangingCodeTransformer extends CodeTransformer { self =>
  import base._
  import Quasiquotes._
  def transform[T,C](code: Code[T,C]): Code[T,C] = {
    val T = code.Typ
    transformChangingType(code) match {
      case code"$code: $$T" => code
      case newCode =>
        System.err.println(s"Top-level type ${T.rep} cannot be changed to ${newCode.Typ.rep}; in: $code ~> $newCode")
        code
    }
  }
  def transformChangingType[T,C](code: Code[T,C]): Code[_,C]
}
