package autodiff

import scala.sys
import autodiff.ast._
import matryoshka.{Corecursive, Recursive}
import matryoshka.implicits._
import scalaz._
import Scalaz._
import scalaz.Liskov._

object evaluate {

  def reduce[T, U](e: T)(implicit TR: Recursive.Aux[T, ExprF],
                         TC: Corecursive.Aux[T, ExprF],
                         UC: Corecursive.Aux[U, CommonF]): U = {
    import ExprF._

    def coalgebraicGTransform: ExprF[T] => CommonF[Free[CommonF, T]] = {
      case commonExprF(e) => e.map(Free.point)
      case extendedExprF(PartialF(t, varName)) =>
        t.project match {
          case commonExprF(FloatVarF(`varName`)) =>
            // 1
            floatConstF(1d)
          case commonExprF(FloatVarF(_)) =>
            // 0
            floatConstF(0d)
          case commonExprF(FloatConstF(_)) =>
            // 0
            floatConstF(0d)
          case commonExprF(NegF(f)) =>
            // - f'(x)
            negF(Free.point[CommonF, T](partialF((f, varName))))
          case commonExprF(ExpF(f)) =>
            // exp[f(x)] f'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            prodF(Free.liftF(expF(f)), fp)
          case commonExprF(LogF(f)) =>
            // f'(x) / f(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            divF(fp, Free.point[CommonF, T](f))
          case commonExprF(SinF(f)) =>
            // cos[f(x)] f'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            prodF(Free.liftF(cosF(f)), fp)
          case commonExprF(CosF(f)) =>
            // - sin[f(x)] f'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            prodF(Free.roll(negF(Free.liftF(sinF(f)))), fp)
          case commonExprF(AddF(f, g)) =>
            // f'(x) + g'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            val gp = Free.point[CommonF, T](partialF((g, varName)))
            addF(fp, gp)
          case commonExprF(SubF(f, g)) =>
            // f'(x) - g'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            val gp = Free.point[CommonF, T](partialF((g, varName)))
            subF(fp, gp)
          case commonExprF(ProdF(f, g)) =>
            // f'(x) g(x) + f(x) g'(x)
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            val gp = Free.point[CommonF, T](partialF((g, varName)))
            val fpG = Free.roll(prodF(fp, Free.point[CommonF, T](g)))
            val fGp = Free.roll(prodF(Free.point[CommonF, T](f), gp))
            addF(fpG, fGp)
          case commonExprF(DivF(f, g)) =>
            // [f'(x) g(x) - f(x) g'(x)] / g(x)^2
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            val gp = Free.point[CommonF, T](partialF((g, varName)))
            val fpG = Free.roll(prodF(fp, Free.point[CommonF, T](g)))
            val fGp = Free.roll(prodF(Free.point[CommonF, T](f), gp))
            val gG = Free.roll(
              prodF(Free.point[CommonF, T](g), Free.point[CommonF, T](g)))
            divF(Free.roll(subF(fpG, fGp)), gG)
          case commonExprF(PowF(f, g)) =>
            // f(x)^[g(x) - 1] [f'(x) g(x) + Log[f(x)] f(x) g'(x)]
            val fp = Free.point[CommonF, T](partialF((f, varName)))
            val gp = Free.point[CommonF, T](partialF((g, varName)))
            val fpG = Free.roll(prodF(fp, Free.point[CommonF, T](g)))
            val fGp = Free.roll(prodF(Free.point[CommonF, T](f), gp))
            val logf = Free.liftF(logF(f))
            val logfFGp = Free.roll(prodF(logf, fGp))
            val fpGAddLogfFGp = Free.roll(addF(fpG, logfFGp))
            val one = Free.liftF(floatConstF[T](1d))
            val gSubOne = Free.roll(subF(Free.point[CommonF, T](g), one))
            val fPowGSubOne =
              Free.roll(powF(Free.point[CommonF, T](f), gSubOne))
            prodF(fPowGSubOne, fpGAddLogfFGp)
          case extendedExprF(PartialF(t, varName)) =>
            sys.error("higher-order derivatives not yet supported.")
        }
    }

    e.transFutu(coalgebraicGTransform)
  }

}
