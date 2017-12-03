package squid.ir.fastanf

import squid.utils.Bool

import scala.collection.mutable

trait Effects {
  protected val pureMtds = mutable.Set[MethodSymbol]()
  //protected val pureTyps = mutable.Set[TypeSymbol]()

  def addPureMtd(m: MethodSymbol): Unit = pureMtds += m
  //def addPureTyp(t: TypeSymbol): Unit = pureTyps += t

  def isPure(r: Rep): Boolean = effect(r) == Pure
  def isPure(d: Def): Boolean = defEffect(d) == Pure
  
  def effect(d: Def): Effect = defEffect(d)

  def effect(r: Rep): Effect = r match {
    case lb: LetBinding => defEffect(lb.value) |+| effect(lb.body)

    //case s: Symbol => s.owner match {
    //  case lb: LetBinding => effect(lb)
    //  case _ => Pure
    //}
    case _: Symbol => Pure

    case Ascribe(r, _) => effect(r)

    case Module(r, _, _) => effect(r)

    case Constant(_) | _: Symbol |
         StaticModule(_) | NewObject(_) |
         Hole(_, _) | SplicedHole(_, _) |
         HOPHole(_, _, _, _) | HOPHole2(_, _, _, _) => Pure
  }

  def mtdEffect(m: MethodSymbol): Effect = {
    //println(m)
    if (pureMtds contains m) Pure else Impure
  }

  def defEffect(d: Def): Effect = d match {
    case l: Lambda => effect(l.body)
    case ma: MethodApp =>
      val selfEff = effect(ma.self)
      val argssEff = ma.argss.argssList.map(effect).fold(Pure)(_ |+| _)
      val mtdEff = mtdEffect(ma.mtd)
      selfEff |+| argssEff |+| mtdEff
    case DefHole(_) => Impure
  }

  sealed trait Effect {
    def |+|(e: Effect): Effect
  }

  case object Pure extends Effect {
    def |+|(e: Effect): Effect = e
  }

  case object Impure extends Effect {
    def |+|(e: Effect): Effect = Impure
  }
}

trait StandardEffects extends Effects {
  addPureMtd(MethodSymbol(TypeSymbol("scala.Int"),"$plus"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Double"),"$plus"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Int"),"$times"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Double"),"$times"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Double"),"div"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Int"), "toDouble"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Double"), "toInt"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Int"), "toFloat"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Option$"), "apply"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Option"), "get"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Tuple2$"), "apply"))
  addPureMtd(MethodSymbol(TypeSymbol("scala.Tuple3$"), "apply"))
  addPureMtd(MethodSymbol(TypeSymbol("squid.lib.package$"),"uncurried2"))
}
