// Copyright 2018 EPFL DATA Lab (data.epfl.ch)
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
package lang

import squid.quasi.DefaultQuasiConfig
import squid.quasi.QuasiConfig

trait CrossStageEnabled extends Base { base =>
  
  def crossStage(value: Any, trep: TypeRep): Rep
  
  // Note: this only really makes sense in an InspectableBase; but we can make it return None in other cases
  def extractCrossStage(r: Rep): Option[Any]
  
  object CrossStage {
    def apply[T: CodeType](v: T): Code[T,Any] = `internal Code`(crossStage(v, typeRepOf[T]))
    def unapply[T](c: Code[T,_]): Option[T] = extractCrossStage(c.rep).asInstanceOf[Option[T]]
  }
  
  trait CrossStageEnabledPredef[QC <: QuasiConfig] extends Predef[QC] {
    val CrossStage = base.CrossStage
  }
  override val Predef = new Predef[DefaultQuasiConfig] with CrossStageEnabledPredef[DefaultQuasiConfig]
  
}
