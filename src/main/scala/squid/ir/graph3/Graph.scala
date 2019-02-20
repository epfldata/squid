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

package squid.ir
package graph3

import squid.utils._
import squid.utils.CollectionUtils.MutSetHelper
import squid.utils.meta.{RuntimeUniverseHelpers => ruh}

import scala.collection.immutable.ListSet
import scala.collection.mutable

/*

TODO:
  - insert Stop nodes at the right places when reifying lambdas...

Possible imporvements:
  - an unrolling factor which needs parametrizing tokens and branches, allowing to push a stop past a branch of the same Val

*/
class Graph extends AST with GraphScheduling with GraphRewriting with CurryEncoding { graph =>
  
  override protected def freshNameImpl(n: Int) = "$"+n
  
  override def showVal(v: BoundVal): String = v.toString
  
  object CallId {
    private var curId = 0; def reset(): Unit = curId = 0
  }
  class CallId(val v: Val) {
    val uid: Int = CallId.curId alsoDo (CallId.curId += 1)
    //def uidstr: String = s"${v.name}$uid"
    def uidstr: String = s"$v$uid"
    override def toString: String = uidstr
  }
  
  //abstract class Node(val bound: Val) {
  sealed abstract class Node {
    def children: Iterator[Rep]
    def typ: TypeRep
    def mkRep = new Rep(this)
  }
  class Rep(var node: Node) {
    
    // TODO check all usages; there might be obsolete usages of this, which is now...
    /** Only used for debuggability, to give a nice name to the Rep. */
    val bound: Val = freshBoundVal(typ)
    
    def showGraph = graph.showGraph(this)
    def showFullGraph = showGraph // TODO
    def eval = graph.eval(this)
    def typ: TypeRep = node.typ
    
    def fullString = toString // TODO
    
    override def toString = s"$bound = $node"
  }
  object Rep {
    def unapply(r: Rep): Some[Node] = Some(r.node)
  }
  //case class ConcreteNode(dfn: Def) extends Node(freshBoundVal(dfn.typ)) {
  case class ConcreteNode(dfn: Def) extends Node {
    def typ: TypeRep = dfn.typ
    def children = dfn.children
    override def toString = s"$dfn"
  }
  //case class Branch(cid: CallId, lhs: Rep, rhs: Rep) extends Node(freshBoundVal(ruh.uni.lub(lhs.typ.tpe::rhs.typ.tpe::Nil))) {
  case class Box(ctrl: Control, body: Rep) extends Node {
    def typ: TypeRep = body.typ
    def children: Iterator[Rep] = Iterator(body)
    //override def toString = s"$bound = [$cid? ${lhs.bound} ¿ ${rhs.bound}]"
  }
  object Box {
    def rep(ctrl: Control, body: Rep): Rep = if (ctrl === Id) body else Box(ctrl, body).mkRep
  }
  //case class Branch(cid: CallId, lhs: Rep, rhs: Rep) extends Node(freshBoundVal(ruh.uni.lub(lhs.typ.tpe::rhs.typ.tpe::Nil))) {
  //case class Branch(ctrl: Option[Control], cid: CallId, lhs: Rep, rhs: Rep) extends Node {
  case class Branch(ctrl: Control, cid: CallId, lhs: Rep, rhs: Rep) extends Node {
    def typ: TypeRep = ruh.uni.lub(lhs.typ.tpe::rhs.typ.tpe::Nil)
    def children: Iterator[Rep] = Iterator(lhs,rhs)
    override def toString = s"[$cid? ${lhs.bound} ¿ ${rhs.bound}]"
  }
  
  
  sealed abstract class Control {
    def toList: List[Control] = this match {
      case End(_, rest) => this :: rest.toList
      case _ => this :: Nil
    }
  }
  case class Begin(cid: CallId) extends Control {
  }
  case class End(cid: CallId, rest: Control) extends Control {
  }
  case class Block(cid: CallId) extends Control {
  }
  case object Id extends Control {
  }
  
  
  //def dfn(r: Rep): Def = r.dfn
  def dfn(r: Rep): Def = r.bound
  //def rep(dfn: Def) = new Rep(dfn, dfn.children.toList)
  def rep(dfn: Def) = dfn match {
    case v: Val if reificationContext.contains(v) => reificationContext(v)
    case _ => new Rep(ConcreteNode(dfn))
  }
  //def simpleRep(dfn: Def): Rep = rep(dfn)
  def repType(r: Rep) = r.typ
  
  
  
  val reificationContext = mutable.Map.empty[Val,Rep]
  
  def letinImpl(bound: BoundVal, value: Rep, mkBody: => Rep) = { 
    require(!reificationContext.contains(bound))
    try {
      reificationContext += bound -> value
      mkBody
    } finally reificationContext -= bound 
  }
  
  override def letin(_bound: BoundVal, value: Rep, body: => Rep, bodyType: TypeRep) =
    letinImpl(_bound, new Rep(value.node) { override val bound = _bound }, body)
  
  override def abs(param: BoundVal, body: => Rep): Rep = {
    val occ = param.toRep
    lambdaVariableOccurrences.put(param, occ)
    letinImpl(param, occ, super.abs(param, body) also {lambdaVariableBindings.put(param,_)})
  }
  
  //class MirrorVal(v: Val) extends BoundVal("@"+v.name)(v.typ,Nil)
  protected val lambdaVariableOccurrences = new java.util.WeakHashMap[Val,Rep]
  protected val lambdaVariableBindings = new java.util.WeakHashMap[Val,Rep]
  // ^ TODO: use a more precise RepOf[NodeSubtype] type
  
  // TODO only evaluate mkArg if the variable actually occurs (cf. mandated semantics of Squid)
  override def substituteVal(r: Rep, v: BoundVal, mkArg: => Rep): Rep = {
    val cid = new CallId(v)
    
    val occ = Option(lambdaVariableOccurrences.get(v)).getOrElse(???) // TODO B/E
    val newOcc = v.toRep
    lambdaVariableOccurrences.put(v,newOcc)
    
    //val abs = Option(lambdaVariableBindings.get(v)).getOrElse(???).node.asInstanceOf[ConcreteNode].asInstanceOf[Abs] // TODO B/E
    val lam = Option(lambdaVariableBindings.get(v)).getOrElse(???) // TODO B/E
    //assert(abs.node.asInstanceOf[ConcreteNode].dfn.isInstanceOf[Abs])
    val abs = lam.node.asInstanceOf[ConcreteNode].dfn.asInstanceOf[Abs]
    
    //println(s". $v . $occ . $newOcc . $lam . $abs . ${abs.body.showGraph}")
    
    // We replace the old Abs node... which should now be garbage-collected.
    // We do this because AST#Abs' body is not mutable
    
    //abs.body.node = Box(Block(cid), abs.body.node.mkRep)
    lam.node = ConcreteNode(Abs(v, Box(Block(cid), abs.body).mkRep)(abs.typ))
    
    val arg = mkArg
    //val bran = Branch(None, cid, Box(End(cid),arg).mkRep, newOcc)
    val bran = Branch(Id, cid, Box(End(cid,Id),arg).mkRep, newOcc)
    occ.node = bran
    
    //println(s". $v . $occ . $newOcc . $lam . $abs . ${abs.body.showGraph}")
    
    Box(Begin(cid), r).mkRep
  }
  
  
  def iterator(r: Rep): Iterator[Rep] = mkIterator(r)(false,mutable.HashSet.empty)
  def mkIterator(r: Rep)(implicit rev: Bool, done: mutable.HashSet[Rep]): Iterator[Rep] = done.setAndIfUnset(r, {
    Iterator.single(r) ++ r.node.children.flatMap(mkIterator)
  }, Iterator.empty)
  
  def showGraph(rep: Rep, full: Bool = false): String = s"$rep" + {
    val defsStr = iterator(rep).toList.distinct.filterNot(_ === rep).collect {
      // TODO use 'full'
      case r => s"\n\t$r;"
      //case r if full =>
      //  s"\n\t${r.bound} = ${r.boundTo.mkString(false,false)};"
      //case r @ Rep(ConcreteNode(d)) if !d.isSimple => s"\n\t${r.bound} = ${d};"
    }.mkString
    if (defsStr.isEmpty) "" else " where:" + defsStr
  }
  
  implicit class GraphDefOps(private val self: Def) {
    def isSimple = self match {
      //case _: SyntheticVal => false  // actually considered trivial?
      case _: LeafDef => true
      //case Bottom => true
      case _ => false
    }
  }
  
  
  override def prettyPrint(d: Def) = (new DefPrettyPrinter)(d)
  class DefPrettyPrinter(showInlineNames: Bool = true, showInlineCF:Bool = true) extends super.DefPrettyPrinter {
    val printed = mutable.Set.empty[Rep]
    override val showValTypes = false
    override val desugarLetBindings = false
    var curCol = Console.BLACK
    //override def apply(r: Rep): String = printed.setAndIfUnset(r, (r.boundTo match {
    //  case _ if !showInlineCF => super.apply(r.bound)
    //  case ConcreteNode(d) if !d.isSimple => super.apply(r.bound)
    //  case n => (if (showInlineNames) Debug.GREY +r.bound+":" + curCol else "")+apply(n)
    //}) alsoDo {printed -= r}, s"[RECURSIVE ${super.apply(r.bound)}]")
    //override def apply(d: Def): String = d match {
    //  case Bottom => "⊥"
    //  case MirrorVal(v) => s"<$v>"
    //  case _ => super.apply(d)
    //}
    //def apply(n: Node): String = n match {
    //  case Pass(cid, res) =>
    //    val col = colorOf(cid)
    //    s"$col⟦$cid⟧$curCol ${res |> apply}"
    //  case Call(cid, res) =>
    //    val col = colorOf(cid)
    //    s"$col⟦$cid$curCol ${res |> apply}$col⟧$curCol"
    //  case Arg(cid, res) =>
    //    val col = colorOf(cid)
    //    //s"$col$cid⟨⟩$curCol${res|>apply}"
    //    s"⟦$col$cid⟧$curCol${res|>apply}"
    //  case Branch(Condition(ops,cid), cbr, els) =>
    //    val oldCol = curCol
    //    curCol = colorOf(cid)
    //    //s"${cid}⟨${cbr |> apply}⟩$oldCol${curCol = oldCol; apply(els)}"
    //    s"(${ops.map{case(k,c)=>s"$k$c;"}.mkString}$curCol$cid ? ${cbr |> apply} ¿ $oldCol${curCol = oldCol; apply(els)})"
    //  case cn@ConcreteNode(v:Val) => apply(cn.mkRep)
    //  case ConcreteNode(d) => apply(d)
    //}
  }
  
  
  
}

