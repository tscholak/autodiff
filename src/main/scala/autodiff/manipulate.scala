package autodiff

import scala.{::, Double, Int, Nil, Option, Some}
import scala.Predef.{ArrowAssoc, Map, String}
import scala.math._
import autodiff.ast._
import matryoshka.{AlgebraM, Birecursive, Corecursive, EndoTransform, Recursive}
import matryoshka.implicits._

import scalaz._
import Scalaz._
import scalaz.Liskov._

object manipulate {

  def evaluate[T](e: T)(implicit T: Birecursive.Aux[T, CommonF]): State[Map[String, Double], Option[Double]] = {

    val S = StateT.stateMonad[Map[String, Double]]
    import S._

    def algebra: AlgebraM[State[Map[String, Double], ?], CommonF, Option[Double]] = {
      case FloatVarF(n)   => for { m <- get } yield m.get(n)
      case FloatConstF(v) => point(Some(v))
      case IdF(x)         => point(x)
      case NegF(x)        => point(x.map(-_))
      case ExpF(x)        => point(x.map(exp))
      case LogF(x)        => point(x.map(log))
      case SinF(x)        => point(x.map(sin))
      case CosF(x)        => point(x.map(cos))
      case AddF(x, y)     => point((x ⊛ y)(_ + _))
      case SubF(x, y)     => point((x ⊛ y)(_ - _))
      case ProdF(x, y)    => point((x ⊛ y)(_ * _))
      case DivF(x, y)     => point((x ⊛ y)(_ / _))
      case PowF(x, y)     => point((x ⊛ y)(pow))
    }

    e.cataM(algebra)
  }

  def simplify[T](e: T)(implicit T: Birecursive.Aux[T, CommonF]): T = {
    val endoTransform: EndoTransform[T, CommonF] = {
      case IdF(x) => x.project
      case e @ ExpF(x) =>
        x.project match {
          case FloatConstF(0d) => FloatConstF(1d)
          case _               => e
        }
      case e @ LogF(x) =>
        x.project match {
          case FloatConstF(1d) => FloatConstF(0d)
          case _               => e
        }
      case e @ SinF(x) =>
        x.project match {
          case FloatConstF(0d) => FloatConstF(0d)
          case _               => e
        }
      case e @ CosF(x) =>
        x.project match {
          case FloatConstF(0d) => FloatConstF(1d)
          case _               => e
        }
      case e @ AddF(x, y) =>
        (x.project, y.project) match {
          case (FloatConstF(v1), FloatConstF(v2)) => FloatConstF(v1 + v2)
          case (FloatConstF(0d), y)               => y
          case (x, FloatConstF(0d))               => x
          case _                                  => e
        }
      case e @ SubF(x, y) =>
        (x.project, y.project) match {
          case (FloatConstF(v1), FloatConstF(v2)) => FloatConstF(v1 - v2)
          case (FloatConstF(0d), _)               => NegF(y)
          case (x, FloatConstF(0d))               => x
          case _                                  => e
        }
      case e @ ProdF(x, y) =>
        (x.project, y.project) match {
          // case (FloatConstF(0d), _) => FloatConstF(0d)
          // case (_, FloatConstF(0d)) => FloatConstF(0d)
          case (FloatConstF(v1), FloatConstF(v2)) => FloatConstF(v1 * v2)
          case (FloatConstF(1d), y)               => y
          case (x, FloatConstF(1d))               => x
          case _                                  => e
        }
      case e @ DivF(x, y) =>
        (x.project, y.project) match {
          // case (FloatConstF(0d), _) => FloatConstF(0d)
          case (FloatConstF(v1), FloatConstF(v2)) => FloatConstF(v1 / v2)
          case (x, FloatConstF(1d))               => x
          case _                                  => e
        }
      case e @ PowF(x, y) =>
        (x.project, y.project) match {
          // case (x, FloatConstF(0d)) => FloatConstF(1d)
          case (x, FloatConstF(1d)) => x
          case _                    => e
        }
      case e => e
    }

    e.transCata[T](endoTransform)
  }

  def reduce[T, U](
      e: T)(implicit TR: Recursive.Aux[T, ExprF], TC: Corecursive.Aux[T, ExprF], UC: Corecursive.Aux[U, CommonF]): U = {
    import ExprF._

    def aux(vars: Map[String, Int])(t: T, tp: String => T): CommonF[Free[CommonF, T]] = {
      idF(Free.point[CommonF, T](vars.toList match {
        case (name, n) :: tl if n > 1 =>
          partialF((tp(name), ((name -> (n - 1)) :: tl).toMap))
        case (name, n) :: tl if n == 1 =>
          partialF((tp(name), tl.toMap))
        case _ :: tl =>
          partialF((t, tl.toMap))
        case Nil =>
          t
      }))
    }

    def coalgebraicGTransform: ExprF[T] => CommonF[Free[CommonF, T]] = {
      case commonExprF(e) => e.map(Free.point)
      case extendedExprF(PartialF(t, vars)) =>
        t.project match {
          case commonExprF(FloatVarF(name)) if vars.get(name).exists(_ <= 0) =>
            // x
            floatVarF(name)
          case commonExprF(FloatVarF(name)) if vars.get(name).contains(1) =>
            // 1
            floatConstF(1d)
          case commonExprF(FloatVarF(_)) =>
            // 0
            floatConstF(0d)
          case commonExprF(FloatConstF(_)) =>
            // 0
            floatConstF(0d)
          case commonExprF(IdF(f)) =>
            // f'(x)
            idF(Free.point[CommonF, T](partialF((f, vars))))
          case commonExprF(NegF(f)) =>
            // - f'(x)
            negF(Free.point[CommonF, T](partialF((f, vars))))
          case commonExprF(ExpF(f)) =>
            aux(vars)(expF(f), name => {
              // exp[f(x)] f'(x)
              val fp: T = partialF((f, Map(name -> 1)))
              prodF((expF(f): T, fp))
            })
          case commonExprF(LogF(f)) =>
            aux(vars)(logF(f), name => {
              // f'(x) / f(x)
              val fp: T = partialF((f, Map(name -> 1)))
              divF((fp, f))
            })
          case commonExprF(SinF(f)) =>
            aux(vars)(sinF(f), name => {
              // cos[f(x)] f'(x)
              val fp: T = partialF((f, Map(name -> 1)))
              prodF((cosF(f): T, fp))
            })
          case commonExprF(CosF(f)) =>
            aux(vars)(cosF(f), name => {
              // - sin[f(x)] f'(x)
              val fp: T = partialF((f, Map(name -> 1)))
              prodF((negF[T](sinF(f)): T, fp))
            })
          case commonExprF(AddF(f, g)) =>
            aux(vars)(addF((f, g)), name => {
              // f'(x) + g'(x)
              val fp: T = partialF((f, Map(name -> 1)))
              val gp: T = partialF((g, Map(name -> 1)))
              addF((fp, gp))
            })
          case commonExprF(SubF(f, g)) =>
            aux(vars)(subF((f, g)), name => {
              // f'(x) - g'(x)
              val fp: T = partialF((f, Map(name -> 1)))
              val gp: T = partialF((g, Map(name -> 1)))
              subF((fp, gp))
            })
          case commonExprF(ProdF(f, g)) =>
            aux(vars)(
              prodF((f, g)),
              name => {
                // f'(x) g(x) + f(x) g'(x)
                val fp: T = partialF((f, Map(name -> 1)))
                val gp: T = partialF((g, Map(name -> 1)))
                val fpG: T = prodF[T](fp, g)
                val fGp: T = prodF[T](f, gp)
                addF((fpG, fGp))
              }
            )
          case commonExprF(DivF(f, g)) =>
            aux(vars)(
              divF((f, g)),
              name => {
                // [f'(x) g(x) - f(x) g'(x)] / g(x)^2
                val fp: T = partialF((f, Map(name -> 1)))
                val gp: T = partialF((g, Map(name -> 1)))
                val fpG: T = prodF[T](fp, g)
                val fGp: T = prodF[T](f, gp)
                val gG: T = prodF[T](g, g)
                divF[T]((subF[T](fpG, fGp): T, gG))
              }
            )
          case commonExprF(PowF(f, g)) =>
            aux(vars)(
              powF((f, g)),
              name => {
                // f(x)^[g(x) - 1] [f'(x) g(x) + Log[f(x)] f(x) g'(x)]
                val fp: T = partialF((f, Map(name -> 1)))
                val gp: T = partialF((g, Map(name -> 1)))
                val fpG: T = prodF[T](fp, g)
                val fGp: T = prodF[T](f, gp)
                val logf: T = logF(f)
                val logfFGp: T = prodF[T](logf, fGp)
                val fpGAddLogfFGp: T = addF[T](fpG, logfFGp)
                val one: T = floatConstF[T](1d)
                val gSubOne: T = subF[T](g, one)
                val fPowGSubOne: T = powF[T](f, gSubOne)
                prodF[T]((fPowGSubOne, fpGAddLogfFGp))
              }
            )
          case extendedExprF(PartialF(t2, vars2)) =>
            idF(Free.point[CommonF, T](partialF((t2, for {
              (name, n) <- vars
            } yield {
              name -> vars2.get(name).map(_ + n).getOrElse(n)
            }))))
        }
    }

    e.transFutu(coalgebraicGTransform)
  }

}
