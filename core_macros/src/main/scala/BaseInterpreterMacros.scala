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

object BaseInterpreterMacros {
  
  import scala.language.experimental.macros
  
  def genLambdaBody: Any = macro genLambdaBodyImpl
  
  import scala.reflect.macros.blackbox
  
  def genLambdaBodyImpl(c: blackbox.Context) = {
    import c.universe._
    val result =
    q"params match { case ..${
      for (i <- 0 to 22) yield {
        val (vars, params, assigns) = (for (j <- 0 until i) yield {
          val v = TermName(s"x$j")
          val p = TermName(s"p$j")
          (pq"$v", q"val $p: Any", q"$v.value = $p")
        }).unzip3
        cq"List(..${vars}) => (..$params) => {..$assigns; body}"
        /* ^ In Scala 2.12, lambdas are encoded as a special class that Scala's runtime reflection does not seem to be
             able to recognize and load, making it crash with an assertion error;
             we can still create old-fashioned instances of FunctionN using the `new` syntax as below, but this is not a
             general solution, as lambdas could come from any place in the application, not just from the `lambda`
             factory. */
        //cq"""List(..${vars}) =>
        //  new _root_.scala.${TypeName("Function"+i)}[..${(0 to i).map(_ => tq"Any")}] {
        //    def apply(..$params) = {..$assigns; body}
        //  }
        //"""
      }
    }}"
    //println(result)
    result: c.Tree
  }
  
}
