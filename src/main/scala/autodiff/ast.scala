package autodiff

import scala.{Double, Int, Function, StringContext}
import scala.Predef.{implicitly, Map, String}
import matryoshka._
import matryoshka.implicits._
import monocle.Prism
import monocle.macros.Lenses
import scalaz._
import Scalaz._
import scalaz.Liskov._

object ast {

  type ExprF[A] = Coproduct[ExtensionF, CommonF, A]

  val commonExprF: CommonF :<: ExprF = implicitly[CommonF :<: ExprF]
  val extendedExprF: ExtensionF :<: ExprF = implicitly[ExtensionF :<: ExprF]

  object ExprF {

    implicit def fromCommonF[T](e: CommonF[T])(
        implicit TC: Corecursive.Aux[T, ExprF]): T =
      commonExprF(e).embed

    implicit def fromExtensionF[T](e: ExtensionF[T])(
        implicit TC: Corecursive.Aux[T, ExprF]): T =
      extendedExprF(e).embed

  }

  sealed abstract class CommonF[A]

  object CommonF {

    implicit val equal: Delay[Equal, CommonF] = new Delay[Equal, CommonF] {
      override def apply[A](fa: Equal[A]): Equal[CommonF[A]] = {
        implicit val eqA: Equal[A] = fa
        Equal.equal {
          case (FloatVarF(n1), FloatVarF(n2))     => n1 ≟ n2
          case (FloatConstF(v1), FloatConstF(v2)) => v1 ≟ v2
          case (IdF(e1), IdF(e2))                 => e1 ≟ e2
          case (NegF(e1), NegF(e2))               => e1 ≟ e2
          case (ExpF(e1), ExpF(e2))               => e1 ≟ e2
          case (LogF(e1), LogF(e2))               => e1 ≟ e2
          case (SinF(e1), SinF(e2))               => e1 ≟ e2
          case (CosF(e1), CosF(e2))               => e1 ≟ e2
          case (AddF(e1, e2), AddF(e3, e4))       => (e1 ≟ e3) && (e2 ≟ e4)
          case (SubF(e1, e2), SubF(e3, e4))       => (e1 ≟ e3) && (e2 ≟ e4)
          case (ProdF(e1, e2), ProdF(e3, e4))     => (e1 ≟ e3) && (e2 ≟ e4)
          case (DivF(e1, e2), DivF(e3, e4))       => (e1 ≟ e3) && (e2 ≟ e4)
          case (PowF(e1, e2), PowF(e3, e4))       => (e1 ≟ e3) && (e2 ≟ e4)

          case (_, _) => false
        }
      }
    }

    implicit val traverse: Traverse[CommonF] = new Traverse[CommonF] {
      override def traverseImpl[G[_], A, B](fa: CommonF[A])(f: (A) => G[B])(
          implicit evidence$1: Applicative[G]): G[CommonF[B]] = fa match {
        case FloatVarF(n)   => floatVarF[B](n).point[G]
        case FloatConstF(v) => floatConstF[B](v).point[G]
        case IdF(e)         => f(e).map(idF(_))
        case NegF(e)        => f(e).map(negF(_))
        case ExpF(e)        => f(e).map(expF(_))
        case LogF(e)        => f(e).map(logF(_))
        case SinF(e)        => f(e).map(sinF(_))
        case CosF(e)        => f(e).map(cosF(_))
        case AddF(e1, e2)   => (f(e1) ⊛ f(e2))(addF(_, _))
        case SubF(e1, e2)   => (f(e1) ⊛ f(e2))(subF(_, _))
        case ProdF(e1, e2)  => (f(e1) ⊛ f(e2))(prodF(_, _))
        case DivF(e1, e2)   => (f(e1) ⊛ f(e2))(divF(_, _))
        case PowF(e1, e2)   => (f(e1) ⊛ f(e2))(powF(_, _))
      }
    }

    implicit val show: Delay[Show, CommonF] =
      new Delay[Show, CommonF] {
        def apply[F](eq: Show[F]): Show[CommonF[F]] =
          Show.show({
            case FloatVarF(n)   => Cord(s"FloatVarF($n)")
            case FloatConstF(v) => Cord(s"FloatConstF($v)")
            case IdF(v)         => Cord(s"IdF($v)")
            case NegF(v)        => Cord(s"NegF($v)")
            case ExpF(v)        => Cord(s"ExpF($v)")
            case LogF(v)        => Cord(s"LogF($v)")
            case SinF(v)        => Cord(s"SinF($v)")
            case CosF(v)        => Cord(s"CosF($v)")
            case AddF(e1, e2)   => Cord(s"AddF($e1, $e2)")
            case SubF(e1, e2)   => Cord(s"SubF($e1, $e2)")
            case ProdF(e1, e2)  => Cord(s"ProdF($e1, $e2)")
            case DivF(e1, e2)   => Cord(s"DivF($e1, $e2)")
            case PowF(e1, e2)   => Cord(s"PowF($e1, $e2)")
          })
      }

  }

  sealed abstract class ExtensionF[A]

  object ExtensionF {

    implicit val equal: Delay[Equal, ExtensionF] =
      new Delay[Equal, ExtensionF] {
        override def apply[A](fa: Equal[A]): Equal[ExtensionF[A]] = {
          implicit val eqA: Equal[A] = fa
          Equal.equal {
            case (PartialF(e1, vs1), PartialF(e2, vs2)) =>
              (e1 ≟ e2) && (vs1 ≟ vs2)
          }
        }
      }

    implicit val traverse: Traverse[ExtensionF] = new Traverse[ExtensionF] {
      override def traverseImpl[G[_], A, B](fa: ExtensionF[A])(f: (A) => G[B])(
          implicit evidence$1: Applicative[G]): G[ExtensionF[B]] = fa match {
        case PartialF(e, vs) => f(e).map(partialF[B](_, vs))
      }
    }

  }

  @Lenses final case class FloatVarF[A](name: String) extends CommonF[A]

  def floatVarF[A]: Prism[CommonF[A], String] =
    Prism.partial[CommonF[A], String] {
      case FloatVarF(n) => n
    }(FloatVarF.apply)

  @Lenses final case class FloatConstF[A](value: Double) extends CommonF[A]

  def floatConstF[A]: Prism[CommonF[A], Double] =
    Prism.partial[CommonF[A], Double] { case FloatConstF(v) => v }(
      FloatConstF.apply)

  @Lenses final case class IdF[A](expr: A) extends CommonF[A]

  def idF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case IdF(e) => e }(IdF.apply)

  @Lenses final case class NegF[A](expr: A) extends CommonF[A]

  def negF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case NegF(e) => e }(NegF.apply)

  @Lenses final case class ExpF[A](expr: A) extends CommonF[A]

  def expF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case ExpF(e) => e }(ExpF.apply)

  @Lenses final case class LogF[A](expr: A) extends CommonF[A]

  def logF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case LogF(e) => e }(LogF.apply)

  @Lenses final case class SinF[A](expr: A) extends CommonF[A]

  def sinF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case SinF(e) => e }(SinF.apply)

  @Lenses final case class CosF[A](expr: A) extends CommonF[A]

  def cosF[A]: Prism[CommonF[A], A] =
    Prism.partial[CommonF[A], A] { case CosF(e) => e }(CosF.apply)

  @Lenses final case class AddF[A](expr1: A, expr2: A) extends CommonF[A]

  def addF[A]: Prism[CommonF[A], (A, A)] =
    Prism.partial[CommonF[A], (A, A)] { case AddF(e1, e2) => (e1, e2) }(
      Function.tupled(AddF.apply))

  @Lenses final case class SubF[A](expr1: A, expr2: A) extends CommonF[A]

  def subF[A]: Prism[CommonF[A], (A, A)] =
    Prism.partial[CommonF[A], (A, A)] { case SubF(e1, e2) => (e1, e2) }(
      Function.tupled(SubF.apply))

  @Lenses final case class ProdF[A](expr1: A, expr2: A) extends CommonF[A]

  def prodF[A]: Prism[CommonF[A], (A, A)] =
    Prism.partial[CommonF[A], (A, A)] { case ProdF(e1, e2) => (e1, e2) }(
      Function.tupled(ProdF.apply))

  @Lenses final case class DivF[A](expr1: A, expr2: A) extends CommonF[A]

  def divF[A]: Prism[CommonF[A], (A, A)] =
    Prism.partial[CommonF[A], (A, A)] { case DivF(e1, e2) => (e1, e2) }(
      Function.tupled(DivF.apply))

  @Lenses final case class PowF[A](expr1: A, expr2: A) extends CommonF[A]

  def powF[A]: Prism[CommonF[A], (A, A)] =
    Prism.partial[CommonF[A], (A, A)] { case PowF(e1, e2) => (e1, e2) }(
      Function.tupled(PowF.apply))

  @Lenses final case class PartialF[A](expr: A, vars: Map[String, Int])
      extends ExtensionF[A]

  def partialF[A]: Prism[ExtensionF[A], (A, Map[String, Int])] =
    Prism.partial[ExtensionF[A], (A, Map[String, Int])] {
      case PartialF(e, vars) => (e, vars)
    }(Function.tupled(PartialF.apply))

}
