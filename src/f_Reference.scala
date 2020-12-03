import scala.annotation.tailrec

object f_Reference extends App {

  case class wp(sto: Map[Int, value], t: term)

  trait Type

  case object UnitType extends Type

  case object NumType extends Type

  case class FunType(ty1: Type, ty2: Type) extends Type

  case class RefType(t: Type) extends Type

  trait term

  case class Let(x: String, t: term, in: term) extends term

  case class Var(x: String) extends term

  case class App(f: term, p: term) extends term

  case class Seq(t1: term, t2: term) extends term

  case class Ref(t: term) extends term

  case class Deref(t: term) extends term

  case class Assign(l: term, r: term) extends term

  trait value extends term

  case object UnitV extends value

  case class NumV(n: Int) extends value

  case class Fun(x: String, ty: Type, t: term) extends value

  case class Addr(p: Int) extends value

  def substitution(t: term, from: String, to: term): term = t match {
    case UnitV => UnitV
    case NumV(n) => NumV(n)
    case Let(x, t, in) => Let(x, substitution(t, from, to), substitution(in, from, to))
    case Var(x) => if (x == from) to else Var(x)
    case Fun(x, ty, t) => if (x == from) Fun(x, ty, t) else Fun(x, ty, substitution(t, from, to))
    case App(f, p) => App(substitution(f, from, to), substitution(p, from, to))
    case Seq(t1, t2) => Seq(substitution(t1, from, to), substitution(t2, from, to))
    case Ref(t) => Ref(substitution(t, from, to))
    case Deref(t) => Deref(substitution(t, from, to))
    case Assign(l, r) => Assign(substitution(l, from, to), substitution(r, from, to))
    case Addr(p) => Addr(p)
  }

  def type_check(m: Map[String, Type], rm: Map[Int, Type], t: term): Type = t match {
    case UnitV => UnitType
    case NumV(_) => NumType
    case Let(x, t, in) => type_check(m + (x -> type_check(m, rm, t)), rm, in)
    case Var(x) => m(x)
    case Fun(x, ty, t) => FunType(ty, type_check(m + (x -> ty), rm, t))
    case App(f, p) => type_check(m, rm, f) match {
      case FunType(ty1, ty2) if ty1 == type_check(m, rm, p) => ty2
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Seq(t1, t2) => type_check(m, rm, t1) match {
      case UnitType => type_check(m, rm, t2)
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Ref(t) => RefType(type_check(m, rm, t))
    case Deref(ty) => type_check(m, rm, ty) match {
      case RefType(ty) => ty
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Assign(l, r) => type_check(m, rm, l) match {
      case RefType(ty) if type_check(m, rm, r) == ty => UnitType
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Addr(p) => RefType(rm(p))
  }

  @tailrec
  def find_addr(sto: Map[Int, value], n: Int): Int = if (sto.contains(n)) find_addr(sto, n + 1) else n

  def find_addr(sto: Map[Int, value]): Int = find_addr(sto, 0)

  def reduce(sto: Map[Int, value], t: term): wp = t match {
    case v: value => wp(sto, v)
    case Let(x, t, in) => t match {
      case v: value => wp(sto, substitution(in, x, v))
      case _ =>
        val w = reduce(sto, t)
        wp(w.sto, Let(x, w.t, in))
    }
    case App(f, p) => f match {
      case Fun(x, _, t) => wp(sto, substitution(t, x, p))
      case _ =>
        val w = reduce(sto, f)
        wp(w.sto, App(w.t, p))
    }
    case Seq(t1, t2) => t1 match {
      case UnitV => wp(sto, t2)
      case _ =>
        val w = reduce(sto, t1)
        wp(w.sto, Seq(w.t, t2))
    }
    case Ref(t) => t match {
      case v: value =>
        val p = find_addr(sto)
        wp(sto + (p -> v), Addr(p))
      case _ =>
        val w = reduce(sto, t)
        wp(w.sto, Ref(w.t))
    }
    case Deref(t) => t match {
      case Addr(p) => wp(sto, sto(p))
      case _ =>
        val w = reduce(sto, t)
        wp(w.sto, Deref(w.t))
    }
    case Assign(l, r) => l match {
      case Addr(p) => r match {
        case v: value => wp(sto + (p -> v), UnitV)
        case _ =>
          val w = reduce(sto, r)
          wp(w.sto, Assign(l, w.t))
      }
      case _ =>
        val w = reduce(sto, l)
        wp(w.sto, Assign(w.t, r))
    }
  }

  def concrete(ty: Type): String = ty match {
    case UnitType => "Unit"
    case NumType => "Num"
    case FunType(ty1, ty2) => concrete(ty1) + "->" + concrete(ty2)
    case RefType(t) => "Ref(" + concrete(t) + ")"
  }

  def concrete(t: term): String = t match {
    case UnitV => "unit"
    case NumV(n) => n + ""
    case Let(x, t, in) => x + " = " + concrete(t) + " in " + concrete(in)
    case Var(x) => x
    case Fun(x, ty, t) => "{^" + x + ":" + concrete(ty) + "." + concrete(t) + "}"
    case App(f, p) => concrete(f) + " " + (p match {
      case App(_, _) => "(" + concrete(p) + ")"
      case _ => concrete(p)
    })
    case Seq(t1, t2) => concrete(t1) + ";" + concrete(t2)
    case Ref(t) => "Ref(" + concrete(t) + ")"
    case Deref(t) => "*(" + concrete(t) + ")"
    case Assign(l, r) => concrete(l) + ":=" + concrete(r)
    case Addr(p) => "" + p
  }

  def full_reduce(t: term): term = full_reduce(Map(), t, 0)

  @tailrec
  def full_reduce(m: Map[Int, value], t: term, i: Int): term = {
    println(i + ": \n\t" + concrete(t))
    val w = reduce(m, t)
    w.t match {
      case res if res == t =>
        println("Normal Form:\n\t" + concrete(res))
        println("total step: " + i)
        res
      case res => full_reduce(w.sto, res, i + 1)
    }
  }

  def test(t: term): Unit = {
    println(concrete(t))
    println(concrete(type_check(Map(), Map(), t)))
    full_reduce(t)
  }

  val t1 = Deref(Ref(NumV(5)))
//  test(t1)

  val t2 = Seq(Assign(Var("x"), NumV(10)), Deref(Var("x")))

  val t3 = Let("x", Ref(NumV(5)), t2)
  test(t3)
}
