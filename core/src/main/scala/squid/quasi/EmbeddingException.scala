// Copyright 2019 EPFL DATA Lab (data.epfl.ch)
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
package quasi

sealed class EmbeddingException(val msg: String) extends Exception(msg)
object EmbeddingException {
  def apply(msg: String) = new EmbeddingException(msg)
  def unapply(ee: EmbeddingException) = Some(ee.msg)
  case class Typing(typeError: String) extends EmbeddingException("Quoted expression does not type check: "+typeError)
  case class Unsupported(featureName: String) extends EmbeddingException(s"Unsupported feature: $featureName")
}
