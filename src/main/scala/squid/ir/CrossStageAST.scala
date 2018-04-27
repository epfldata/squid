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
package ir

import squid.utils._
import squid.lang.CrossStageEnabled

trait CrossStageAST extends AST with CrossStageEnabled {
  
  // make `crossStage` method public, officially enabling construction of cross-stage nodes
  override def crossStage(value: Any, trep: TypeRep): Rep = super.crossStage(value, trep)
  
}
