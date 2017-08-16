package autodiff

import scala.App
import autodiff.ast._
import matryoshka.data.Nu
import matryoshka.Corecursive
import matryoshka.implicits._

import scalaz._
import Scalaz._

object yolo extends App {

  def expr[T](implicit TC: Corecursive.Aux[T, ExprF]): T = {
    import ExprF._
    partialF[T]((sinF[T](floatVarF[T]("x", 15d)), "x"))
    // partialF[T]((partialF[T]((sinF[T](floatVarF[T]("x", 15d)), "x")), "x"))
  }

  val reduced: Nu[CommonF] = evaluate.reduce[Nu[ExprF], Nu[CommonF]](expr[Nu[ExprF]])

  reduced.println

}