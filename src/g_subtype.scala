import scala.annotation.tailrec

object g_subtype extends App {

  trait Type

  case object TopType extends Type

  case object BoolType  extends Type

  case object NumType extends Type

  case class ArrType(pty: Type, tty: Type) extends Type

  case class RecType(m: Map[String, Type]) extends Type

  trait Term

  case object UnitTerm extends Term

  case class Bool(b: Boolean) extends Term

  case class Num(n: Int)  extends Term

  case class Var(x: String) extends Term

  case class Abs(x: String, ty: Type, t: Term) extends Term

  case class App(t1: Term, t2: Term) extends Term

  case class Rec(m: Map[String, Term]) extends Term

  case class Prj(t: Term, l: String) extends Term

  //  case Num(n)
  //  case Var(x)
  //  case Abs(x, ty, t1)
  //  case App(t1, t2)
  //  case Rec(m)
  //  case Prj(t1, l)

  def SubType(ty1: Type, ty2: Type): Boolean = (ty1, ty2) match {
    case (ty1, ty2) if ty1 == ty2 => true
    case (_, TopType) => true
    case (BoolType, NumType) => true
    case (ArrType(p1, t1), ArrType(p2, t2)) => SubType(p2, p1) && SubType(t1, t2)
    case (RecType(m1), RecType(m2)) => m2.forall(e => m1.get(e._1) match {
      case Some(ty) => SubType(ty, e._2)
      case _ => false
    })
    case _ => false
  }

  def TypeCheck(t: Term): Type = TypeCheck(Map(), t)
  def TypeCheck(env: Map[String, Type], t: Term): Type = t match {
    case UnitTerm => TopType
    case Bool(_) => BoolType
    case Num(_) => NumType
    case Var(x) => env.get(x) match {
      case Some(ty) => ty
      case None => throw new RuntimeException("type check fails at " + Concrete(t))
    }
    case Abs(x, ty, t1) => ArrType(ty, TypeCheck(env + (x->ty), t1))
    case App(t1, t2) => TypeCheck(env, t1) match {
      case ArrType(pty, tty) if SubType(TypeCheck(env, t2), pty) => tty
      case _ => throw new RuntimeException("type check fails at " + Concrete(t))
    }
    case Rec(m) => RecType(m.foldLeft(Map[String, Type]())((m, e) => m + (e._1 -> TypeCheck(env, e._2))))
    case Prj(t1, l) => TypeCheck(env, t1) match {
      case RecType(m) if m.contains(l) => m(l)
      case _ => throw new RuntimeException("type check fails at " + Concrete(t))
    }
  }

  def action(t: Term, f: Term => Term): Term = t match {
    case UnitTerm => UnitTerm
    case Bool(b) => Bool(b)
    case Num(n) => Num(n)
    case Var(x) => Var(x)
    case Abs(x, ty, tin) => Abs(x, ty, f(tin))
    case App(t1, t2) => App(f(t1), f(t2))
    case Rec(m) => Rec(m.foldLeft(Map[String, Term]())((m, e) => m + (e._1 -> f(e._2))))
    case Prj(t1, l) => Prj(f(t1), l)
    case _ => t
  }

  def CoercionBool2Num(t: Term): Term = t match {
    case UnitTerm => UnitTerm
    case Bool(b) => if (b) Num(1) else Num(0)
    case Num(n) => Num(n)
    case Var(x) => Var(x)
    case Abs(x, ty, tin) => Abs(x, ty, CoercionBool2Num(tin))
    case App(t1, t2) => App(CoercionBool2Num(t1), CoercionBool2Num(t2))
    case Rec(m) => Rec(m.foldLeft(Map[String, Term]())((m, e) => m + (e._1 -> CoercionBool2Num(e._2))))
    case Prj(t1, l) => Prj(CoercionBool2Num(t1), l)
    case _ => t
  }

  def Concrete(t: Term): String = t match {
    case UnitTerm => "unit"
    case Bool(b) => b + ""
    case Num(n) => "" + n
    case Var(x) => x
    case Abs(x, _, t1) => "{" + x + ". " + Concrete(t1) + "}"
    case App(t1, t2) => "(" + Concrete(t1) + " " + Concrete(t2) + ")"
    case Rec(m) => m.foldLeft("{ ")((s, e) => s + e._1 + ": " + Concrete(e._2) + " ") + "}"
    case Prj(t1, l) => Concrete(t1) + "." + l
  }

  //test subtype

  val ty1 = RecType(Map("x"->TopType, "y"->ArrType(NumType, NumType)))
  val ty2 = RecType(Map("x"->NumType, "y"->ArrType(TopType, NumType), "z"->TopType))

  val t1 = Rec(Map("x"->UnitTerm, "y"->Abs("x", NumType, Var("x"))))
  val t2 = Rec(Map("x"->Bool(false), "y"->Abs("_", TopType, Num(2)), "z"->UnitTerm))

  def isVal(t: Term): Boolean = t match {
    case UnitTerm => true
    case Num(_) => true
    case Var(_) => false
    case Abs(_, _, _) => true
    case App(_, _) => false
    case Rec(m) => m.forall(e => isVal(e._2))
    case Prj(_, _) => false
  }

  def Substitution(t: Term, from: String, to: Term): Term = t match {
    case Var(x) if x == from => to
    case Abs(x, ty, tin) if x != from => Abs(x, ty, Substitution(tin, from, to))
    case App(t1, t2) => App(Substitution(t1, from, to), Substitution(t2, from, to))
    case Rec(m) => Rec(m.foldLeft(Map[String, Term]())((m, e) => m + (e._1 -> Substitution(e._2, from, to))))
    case Prj(r, l) => Prj(Substitution(r, from, to), l)
    case _ => t
  }

  def mReduce(m: Map[String, Term]): Map[String, Term] = mReduce(m.toList, List()).toMap
  @tailrec
  def mReduce(m: List[(String, Term)], res: List[(String, Term)]): List[(String, Term)] = m match {
    case h :: t => h._2 match {
      case t0 if isVal(t0) => mReduce(t, res :+ h)
      case _ => res ::: (h._1, Reduce(h._2)) :: t
    }
    case Nil => res

  }

  def Reduce(t: Term): Term = t match {
    case t if isVal(t) => t
    case Var(x) => Var(x)
    case App(t1, t2) => t1 match {
      case Abs(x, _, tin) => Substitution(tin, x, t2)
      case _ => App(Reduce(t1), t2)
    }
    case Rec(m) => Rec(mReduce(m))
    case Prj(r, l) => r match {
      case Rec(m) if isVal(Rec(m)) => m(l)
      case _ => Prj(Reduce(r), l)
    }
  }

  def FullReduce(t: Term): Term = FullReduce(t, 0)
  @tailrec
  def FullReduce(t: Term, i: Int): Term = {
    println("\t" + i + ": " + Concrete(t))
    Reduce(t) match {
      case res if res == t => res
      case res => FullReduce(res, i + 1)
    }
  }

  def Test(t: Term): Unit = {
    println(Concrete(t))
    println(TypeCheck(t))
    val coerced = CoercionBool2Num(t)
    println(Concrete(coerced))
    FullReduce(coerced)
  }

  val t3 = Abs("x", ty1, Prj(Var("x"), "x"))

  Test(App(t3, t2))

}
