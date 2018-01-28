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

package squid.quasi

import scala.reflect.macros.ParseException
import scala.reflect.macros.whitebox.Context

class PgrmBuilder[Ctx <: Context](val c: Ctx)(unapply: Boolean) { // TODO simplify interaction with Quasi
  val VARARG_REPEAT_STR = "*"

  import c.universe._

  case class Hole(tree: c.Tree, vararg: Boolean, name: Option[c.Name]) {
    def this(tree: c.Tree, vararg: Boolean) = this(tree, vararg, tree match {
      case Bind(name: Name, _) => Some(name)
      case Ident(name: Name)   => Some(name)
      //case q"$_.${name: Name}"   => Some(name) // equivalent to `Select(_, name: TermName)`
      // ^ disabled this as it was confusing in error messages such as "illegal hole position for ..."
      case _                       => None
    })
  }

  def parseError(msg: String) = c.abort(c.enclosingPosition,
    s"""|Failed to parse DSL code: $msg
        |In macro application:""".stripMargin)
  
  val (holes, tree, hasVarargs) = {
    var hasVarargs = false

    val (args, partsPos) = c.macroApplication match {
      case Apply(internal.reificationSupport.SyntacticTypeApplied(Select(Select(Apply(Select(universe0, _), List(Apply(_, parts0))), interpolator0), method0), _), args0) =>
        val parts1 = parts0.map {
          case lit @ Literal(Constant(s: String)) => s -> lit.pos
          case part                               => c.abort(part.pos, "Quasiquotes can only be used with literal strings")
        }
        (if (unapply) internal.subpatterns(args0.head).get else args0, parts1)
    }

    val (holes, codeParts) = (args zip partsPos.tail map {
      case (tree, (part, pos)) if part startsWith VARARG_REPEAT_STR =>
        hasVarargs = true; new Hole(tree, true) -> part.tail
      case (tree, (part, pos)) => new Hole(tree, false) -> part
    } map {
      case (hole, part) =>
        val freshName = c.freshName(hole.name getOrElse TermName("")).toTermName
        // Note: q"($freshName)$part" will prevent things like var assignment "$x = 42" to work, but prevent mis-parsing two consecutive holes
        //freshName -> hole -> s"$freshName$part" // possible mis-parsing
        freshName -> hole -> s"($freshName)$part" // "$x = 42" not supported
    }).unzip
    
    //println("Parsing: "+(partsPos.head._1 :: codeParts).mkString)
    
    val codeTree = try c.parse((partsPos.head._1 :: codeParts).mkString) catch {
      case ParseException(pos, msg) =>
        val varargInfo = if (hasVarargs) "\nNote: the problem may be caused by a vararg matcher (syntax `$name*`)" else ""
        parseError(msg+varargInfo)
    }
    
    if (codeTree.isEmpty)
      throw EmbeddingException("Empty program fragment.")
    
    (holes.toMap, codeTree, hasVarargs)
  }

}

