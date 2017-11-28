//package sfusion2
//package compiler
//
//import Embedding.Predef._
//import Embedding.Quasicodes._
//import java.io.File
//import java.io.PrintStream
//
//import example.VarNormalizer
//import squid.utils._
//import squid.ir._
//import squid.lang._
//import squid.anf.analysis
//import squid.anf.transfo
//import Embedding.Rep
//import Embedding.{Block, AsBlock, WithResult, GeneralClosure}
////import Embedding.{Block, AsBlock, WithResult, GeneralClosure, ConstantShape}
//
///**
//  * Created by lptk on 14/06/17.
//  */
//
//  object ConstantShape {
//    def unapply[T:CodeType,C](x: IR[Strm[Strm[T]],C]): Option[IR[Strm[T],C]] = x match {
//      case GeneralClosure(clos) =>
//        println(clos)
//        ???
//    }
//  }
