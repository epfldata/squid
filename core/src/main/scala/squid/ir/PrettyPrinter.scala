package squid
package ir

import utils._
import squid.lang.Base
import meta.RuntimeUniverseHelpers._
import sru._

class PrettyPrinter extends Base with TraceDebug {

  override type Rep = Int => String
  override type BoundVal = (String, TypeRep) // (name, type)
  override type TypeRep = TypSymbol
  type TypSymbol = String
  type MtdSymbol = String

  def repEq(a: Rep, b: Rep): Boolean = a == b

  def typLeq(a: TypeRep, b: TypeRep): Boolean = a == b

  val indent = 2
  val SquidLib = "squid.lib.package"

  private def removeBrackets(exp: String): String = exp.drop(1).dropRight(1)

  val escape = (str: String) => str
    .replace("\b", "\\b")
    .replace("\n", "\\n")
    .replace("\t", "\\t")
    .replace("\r", "\\r")
    .replace("\f", "\\f")
    .replace("\"", "\\\"")
    .replace("\\", "\\\\")

  override def bindVal(name: String, typ: TypeRep, annots: List[Annot]): BoundVal = (name, typ)

  override def readVal(v: BoundVal): Rep = offset => v._1 // get the name as string

  override def const(value: Any): Rep = offset => value match {
    case _: Char => s"""'$value'"""
    case v: String => s""""${escape(v)}""""
    case _ => value.toString
  }

  override def lambda(params: List[BoundVal], body: => Rep): Rep = offset => {
    val ps = params.map(p => s"${p._1}: ${p._2}") // map tp "name: Type"
    val plist = ps.mkString(", ") // make list of all params
    s"(($plist) => ${body(offset)})"
  }

  override def staticModule(fullName: String): Rep = offset => fullName

  override def module(prefix: Rep, name: String, typ: TypeRep): Rep = offset => s"${prefix(offset)}.$name"

  override def newObject(tp: TypeRep): Rep = offset => s"new $tp"

  override def letin(bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep): Rep = offset => {
    val b = body(offset)
    val v = value(offset)

    if (bound._2.startsWith("squid.lib.Var")) {
      val tpe = removeBrackets(bound._2.dropWhile(_ != '['))
      " " * offset + s"var ${bound._1}: $tpe = $v\n$b"
    } else {
      " " * offset + s"val ${bound._1}: ${bound._2} = $v\n$b"
    }
  }

  override def ascribe(self: Rep, typ: TypeRep): Rep = offset => s"(${self(offset)}: $typ)"

  override def methodApp(self: Rep, mtd: MtdSymbol, targs: List[TypeRep], args: List[ArgList], tp: TypeRep): Rep = offset => {

    val argumentLists = args.map(_.reps) // Seq[Int => String]
    val arguments = argumentLists.map(seq => seq.map(arg => arg(offset)))

    val tArgList = if (targs.nonEmpty) s"[${targs.mkString(", ")}]" else ""

    val mtdDecoded = sru.TermName(mtd).decodedName

    (self(offset), mtd) match {
      case (SquidLib, "IfThenElse") => {
        val if_ = args.head.reps(0)(offset + indent)
        val then_ = args.head.reps(1)(offset + indent)
        val else_ = args.head.reps(2)(offset + indent)

        val ifStr   = s"if ($if_) {"

        val ifThenStr =
          if (then_.contains("\n")) {
            val s = ifStr :: List(s"$then_", " " * offset + "}")
            s.mkString("\n")
          }
          else {
            val s = ifStr :: List(s"$then_", "}")
            s.mkString(" ")
          }

        val ifThenElseStr =
          if (else_ == "()") {
            ifThenStr
          }
          else if (then_.contains("\n") && else_.contains("\n")) {
            val s = List(ifThenStr + s" else {", s"$else_", " " * offset + "}")
            s.mkString("\n")
          }
          else if (else_.contains("\n")) {
            val s = ifThenStr :: List(" " * offset + s"else {", s"$else_", " " * offset + "}")
            s.mkString("\n")
          }
          else {
            val s = ifThenStr :: List(s"else {", s"$else_", "}")
            s.mkString(" ")
          }

        ifThenElseStr
      }

      case (SquidLib, "While") => {
        val cond_ = args.head.reps(0)(offset + indent)
        val stmt_ = args.head.reps(1)(offset + indent)

        val str = Seq(
          s"while ($cond_) {",
          s"$stmt_"
        )

        if (stmt_.contains("\n"))
          str.mkString("\n") + "\n" + (" " * offset + "}")
        else
          str.mkString(" ")
      }

      case (SquidLib, "Imperative") => {
        val statements = args(0).reps.map(s => s(offset)).mkString("\n")
        val result = args(1).reps.head(offset)

        if (statements != "")
          Seq(
            " " * offset + statements,
            " " * offset + result
          ).mkString("\n")
        else result
      }

      case ("squid.lib.Var", "apply") => args.head.reps.head(offset)

      case ("scala.Symbol", "apply") =>
        // scala.Symbol.apply("arg")
        s"'${removeBrackets(args.head.reps.head(offset))}"

      // apply on tuples should not print the TupleXX[A].apply
      case (s, "apply") if s.startsWith("scala.Tuple") => s"${printArgLists(args, offset)}"

      case (_, "<init>") | (_, "apply") =>
        s"""${self(offset)}$tArgList${printArgLists(args, offset)}"""

      // assignments: replace x.:=(y) with x = y
      case (_, "$colon$eq") if tp == "scala.Unit" =>
        s"""${self(offset)} = ${args.head.reps.head(offset)}"""

      // replace x.! with x
      case (_, "$bang") if targs.isEmpty && args.isEmpty => self(offset)

      case _ => {
        val argStr = printArgLists(args, offset)
        s"""${self(offset)}.$mtdDecoded$tArgList$argStr"""
      }
    }
  }

  val printArgs = (params: ArgList, offset: Int) =>
    (params.reps map (param => param(offset))).mkString("(", ", ", ")")

  val printArgLists = (paramss: List[ArgList], offset: Int) =>
    (paramss map (params => printArgs(params, offset))).mkString

  override def byName(arg: => Rep): Rep = offset => arg(offset)

  def uninterpretedType[A: sru.TypeTag]: TypeRep = sru.typeOf[A].typeSymbol.asType.fullName

  def moduleType(fullName: String): TypeRep = fullName

  def typeApp(self: TypeRep, typ: TypSymbol, targs: List[TypeRep]): TypeRep = typ

  def staticTypeApp(typ: TypSymbol, targs: List[TypeRep]): TypeRep =
    if (targs.nonEmpty) s"$typ[${targs.mkString(", ")}]" else typ

  def recordType(fields: List[(String, TypeRep)]): TypeRep = ???

  def constType(value: Any, underlying: TypeRep): TypeRep = ???

  object Const extends ConstAPI {
    def unapply[T: sru.TypeTag](ir: IR[T, _]): Option[T] = ???
  }

  def hole(name: String, typ: TypeRep): Rep = offset => s"?$name"

  def hopHole(name: String, typ: TypeRep, yes: List[List[BoundVal]], no: List[BoundVal]): Rep = ???

  def splicedHole(name: String, typ: TypeRep): Rep = ???

  def substitute(r: => Rep, defs: scala.collection.immutable.Map[String, Rep]): Rep = ???

  def typeHole(name: String): TypeRep = ???

  /** Parameter `static` should be true only for truly static methods (in the Java sense)
    * Note: index should be None when the symbol is not overloaded, to allow for more efficient caching */
  override def loadMtdSymbol(typ: String, symName: String, index: Option[Int], static: Bool) = symName

  override def loadTypSymbol(fullName: String) = fullName
}
