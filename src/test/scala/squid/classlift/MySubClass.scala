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

package squid.classlift

import squid.quasi._

@dbg_lift
//@lift
class MySubClass(p: Int) extends MyClass2(p + 1, p - 1, p > 0) {
  
  println(p)
  
  def test2 = List(4,5,6)
  //def test2 = List(4,5,p) // FIXME: java.util.NoSuchElementException: None.get
  
  //override def test = super.test ++ test2 // TODO: Embedding Error: Unsupported feature: MySubClass.super
  override def test = test2
  
  var mut2 = {
    //println(p) // FIXME: Embedding Error: Unsupported feature: MySubClass.this.p
    42
  }
  
  def bar(mc: MyClass3) = {
    mc.met + mut2 + mut
  }
  
  println(mut2)
  
}
