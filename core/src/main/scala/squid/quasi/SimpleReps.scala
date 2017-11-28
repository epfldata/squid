package squid
package quasi

import lang.Base

/** Mix this in and import SimplePredef._ to forget about contexts completely! */
trait SimpleReps {  // TODO remove this obsolete trait
self: Base =>
  
  object SimplePredef {
    
    //type Rep[T] = IR[T,Any] // Note: used to be `IR[T,Nothing]`, but it interacted badly with implicit classes (scalac bug)
    type Rep[T] = AnyCode[T]
    
    // For backward compat of some older programs:
    implicit def unsound[T](r: AnyCode[T]): Code[T,Any] = r.asInstanceOf[Code[T,Any]]
    implicit def unsound2[T](r: Code[T,_]): Rep[T] = r.asInstanceOf[Rep[T]]
    
  }
  
}
