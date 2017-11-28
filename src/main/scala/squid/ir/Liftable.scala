package squid
package ir

import quasi._
import squid.lang.Base

/** TODO should probably be put into Base, as it seems to have problems cf implicit w/ contravariant targ; + it's not necessarily best when trying to propagate evidence (cf: ListLift)
  * Note: T should not be contravariant; e.g. when lifting a List[Int], we don't want the possibility to get a node representing a List[Any]!
  * Note: if we want to insert IR[T,C] values via Liftable, we'll actually need a Ctx type variable!! Also, a separate Typ param could make sense (if the value lifts to a different type...) */
trait Liftable[-BaseType <: Base, T] {
  type Typ = T
  def lift(b: BaseType, x: T): b.Rep
}
object Liftable {
  
  class ConstLifter[T: reflect.runtime.universe.TypeTag] extends Liftable[Base, T] { def lift(b: Base, x: Typ): b.Rep = b.const(x) }
  implicit object UnitLift extends ConstLifter[Unit]
  implicit object BooleanLift extends ConstLifter[Boolean]
  implicit object CharLift extends ConstLifter[Char]
  implicit object ShortLift extends ConstLifter[Int]
  implicit object IntLift extends ConstLifter[Int]
  implicit object LongLift extends ConstLifter[Int]
  implicit object FloatLift extends ConstLifter[Double]
  implicit object DoubleLift extends ConstLifter[Double]
  implicit object StringLift extends ConstLifter[String]
  
  implicit def ListLift[B <: Base, T](implicit ev: Liftable[B,T]): Liftable[B, List[T]] = new Liftable[B, List[T]] {
    def lift(b: B, x: Typ): b.Rep = { // TODO use QQ/QC for that
      //val tsym = b.loadTypSymbol("scala.immutable.List")
      //val mtd = b.loadMtdSymbol(tsym, "apply")
      //val mod = b.moduleObject("scala.immutable", false)
      //val obj = b.moduleObject("scala.immutable.List", false)
      //val argLift = implicitly[Liftable[b.type,T]]
      //b.mapp(obj, mtd, b.typeApp(mod, tsym, ???))(???)(b.Args()(x map {a => argLift.lift(b,a)}: _*))
      ???
    }
  }
  
  
}
// TODO merge this with Liftable
trait QuasiLiftable[-BaseType <: Base, T] extends Liftable[BaseType, T] {
  def lift(b: BaseType, x: T): b.Rep = apply(b, x).rep
  def apply(b: BaseType, x: T): b.Code[T,{}]
}
/** TODO a base forwarder to make defining QuasiLiftable instances easier */
object QuasiLiftable {
}













