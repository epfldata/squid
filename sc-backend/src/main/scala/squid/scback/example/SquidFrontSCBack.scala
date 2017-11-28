package squid
package scback
package example

import squid.utils._
import ch.epfl.data.sc._
import pardis._
import deep.scalalib._
import deep.scalalib.collection._
import _root_.squid.ir.SimpleANF

import scala.collection.mutable.ArrayBuffer

/**
  * Created by lptk on 08/11/16.
  */
object SquidFrontSCBack extends App {
  /*_*/
  
  object Frontend extends SimpleANF
  
  object SC extends ir.Base with ScalaCoreOps with PardisBinding.DefaultPardisMixin
  object Backend extends AutoboundPardisIR(SC) with PardisBinding.DefaultRedirections[SC.type]
  def init = Backend.ab = AutoBinder(SC, Backend)  // this is going to generate a big binding structure; put it in a separate file so it's not always recomputed and recompiled!
  init
  
  import Frontend.Predef._
  
  val pgrm = code"val a = ArrayBuffer(1,2,3); a append 1; a.size"
  
  println(pgrm)
  println(pgrm.run)
  
  println(pgrm reinterpretIn Backend)
  
}
