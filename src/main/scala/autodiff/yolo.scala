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

  def expr[T](implicit T: Corecursive.Aux[T, ExprF]): T = {
    import ExprF._
    partialF[T]((sinF[T](prodF[T]((floatVarF[T]("x"), floatVarF[T]("y")))), Map("x" -> 1, "y" -> 1)))
  }

  val reduced: Nu[CommonF] =
    manipulate.reduce[Nu[ExprF], Nu[CommonF]](expr[Nu[ExprF]])

  reduced.println

  val simplified: Nu[CommonF] = manipulate.simplify[Nu[CommonF]](reduced)(pedantic = false)

  simplified.println

  manipulate.evaluate(simplified).run(Map("x" -> 0d, "y" -> 0d)).println

}
