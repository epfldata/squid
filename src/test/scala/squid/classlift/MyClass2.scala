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

class My

@lift
//class MyClass2(val a: Int, var b: Double, c: Boolean) {
class MyClass2(val a: Int, var b: Double, val c: Boolean) extends My {
  def test = List(1,2,3)
  var mut = 42
  def oops = Ooops.oopsy2(this,'hi)
  def foo(mc: MyClass3) = mc.met + mut
}
object MyClass2 {
  
  var mit = 123
  
  class A {
    def oops = Ooops.oopsy2A(this,'hi)
    var mat = 123
  }
  object A
  
  def testo(x: Int) = {
    val mc = new MyClass2(x, 0.0, true)
    Some(mc.mut + x)
  }
  
}

@dbg_lift
//class MyClass4(private val s: Int)
//class MyClass4(private[this] val s: Int)
class MyClass4(val x: Int = 0, name: String) { // FIXME
  print("Hello ")
  println(name)
  //val (x,b) = x->x
  //val (a,b) = x->x
  //def hola = println("¡hola "+name+"!" * x) // FIXME
}
//class MyClass5(val x: Int = 0, st: Int) { // FIXME
//  println(x)
//  val (x,y) = x->x
//}

@lift
class MyClass3 {
  var met = 345
  def getMet(els: Int) = if (met < 0) els else met
  def test = (new MyClass2(1, 2.0, false)).foo(this)
}
object MyClass3 {
}
