package autodiff

import scala.App
import scala.Predef.{ArrowAssoc, Map}
import autodiff.ast._
import matryoshka.data.Nu
import matryoshka.Corecursive
import matryoshka.implicits._

import scalaz._
import Scalaz._

object yolo extends App {

  def expr[T](implicit TC: Corecursive.Aux[T, ExprF]): T = {
    import ExprF._
    partialF[T]((sinF[T](floatVarF[T]("x")), Map("x" -> 2)))
  }

  val reduced: Nu[CommonF] =
    manipulate.reduce[Nu[ExprF], Nu[CommonF]](expr[Nu[ExprF]])

  reduced.println

  manipulate.simplify[Nu[CommonF]](reduced).println

  manipulate.evaluate(reduced).run(Map("x" -> 0d)).println

}
