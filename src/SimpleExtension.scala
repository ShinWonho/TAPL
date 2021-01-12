class SimpleExtension extends TypedLambda {

  import scala.annotation.tailrec

  /* extends System with boolean, number, and record. The system can be Lambda calculus, System F, and so on.  */

  /* Type */

  /* Boolean Type */
  case object Bool extends Type

  /* Number Type */
  case object Num extends Type

  /* Record Type */
  case class Rec(rec: Map[String, Type]) extends Type


  /* Term */

  /* Boolean */
  case class BoolT(b: Boolean) extends Term

  /* If statement */
  case class If(b: Term, th: Term, e: Term) extends Term

  /* Number */
  case class NumT(n: Int) extends Term

  /* Return the successor of n */
  case class Succ(n: Term) extends Term

  /* Record */
  case class RecT(rec: Map[String, Term]) extends Term

  /* Project the Record rec to l */
  case class Prj(rec: Term, l: String) extends Term

  /* Assignment */
  case class Let(x: String, tAssign: Term, tin: Term) extends Term


  /* extends Type Check algorithm */
  override def TypeCheck(env: Map[String, Type], t: Term): Type = t match {
    case BoolT(_) => Bool
    case If(b, th, e) => TypeCheck(env, b) match {
      case Bool =>
        val thty = TypeCheck(env, th)
        val ety = TypeCheck(env, e)
        if (thty == ety) ety
        else throw new RuntimeException("If, then: " + Concrete(thty) +
          " else: " + Concrete(ety) + " in " + Concrete(t))
      case _ => throw new RuntimeException("Not a Bool " + Concrete(b) + " in " + Concrete(t))
    }
    case NumT(_) => Num
    case Succ(n) => TypeCheck(env, n) match {
      case Num => Num
      case ty => throw new RuntimeException("Not a Num " + Concrete(ty) + " in " + Concrete(t))
    }
    case RecT(rec) => Rec(rec.foldLeft(Map[String, Type]())((m, e) => m + (e._1 -> TypeCheck(env, e._2))))
    case Prj(rec, l) => TypeCheck(env, rec) match {
      case Rec(rec) => rec.get(l) match {
        case Some(v) => v
        case None => throw new RuntimeException("No such label " + l + " in " + Concrete(t))
      }
      case ty => throw new RuntimeException("Not a Rec " + Concrete(ty) + " in " + Concrete(t))
    }
    case Let(x, tAssign, tin) => TypeCheck(env + (x->TypeCheck(env, tAssign)), tin)
    case t => super.TypeCheck(env, t)
  }


  /* extends FV */
  override def FV(constraint: Set[String], fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Rec(rec) => rec.foldLeft(Set[String]())((s, e) => s ++ FV(constraint, e._2))

    /* Term */
    case If(b, th, e) => FV(constraint, b) ++ FV(constraint, th) ++ FV(constraint, e)
    case Succ(n) => FV(constraint, n)
    case RecT(rec) => rec.foldLeft(Set[String]())((s, e) => s ++ FV(constraint, e._2))
    case Prj(rec, _) => FV(constraint, rec)
    case Let(x, tAssign, tin) => FV(constraint + x, tAssign) ++ FV(constraint + x, tin)

    case fc => super.FV(constraint, fc)
  }

  /* extends BV */
  override def BV(fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Rec(rec) => rec.foldLeft(Set[String]())((s, e) => s ++ BV(e._2))

    /* Term */
    case If(b, th, e) => BV(b) ++ BV(th) ++ BV(e)
    case Succ(n) => BV(n)
    case RecT(rec) => rec.foldLeft(Set[String]())((s, e) => s ++ BV(e._2))
    case Prj(rec, _) => BV(rec)
    case Let(x, tAssign, tin) => BV(tAssign) ++ BV(tin) + x

    case fc => super.BV(fc)
  }


  /* extends Substitution */
  override def Substitution(t: Term, from: FirstClass, to: FirstClass): Term = t match {
    case t if t == from => to.asInstanceOf[Term]
    case If(b, th, e) =>
      If(Substitution(b, from, to), Substitution(th, from, to), Substitution(e, from, to))
    case Succ(n) => Succ(Substitution(n, from, to))
    case RecT(rec) => RecT(rec.foldLeft(Map[String, Term]())((m, e) => m + (e._1 -> Substitution(e._2, from, to))))
    case Prj(rec, l) => Prj(Substitution(rec, from, to), l)
    case Let(x, tAssign, tin) =>
      /* Let expression also be capture free */
      if (from == Var(x)) Let(x, tAssign, tin)
      else Let(x, Substitution(tAssign, from, to), Substitution(tin, from, to))
    case t => super.Substitution(t, from, to)
  }

  override def Substitution(ty: Type, from: FirstClass, to: FirstClass): Type = ty match {
    case Rec(rec) => Rec(rec.foldLeft(Map[String, Type]())((m, e) => m + (e._1 -> Substitution(e._2, from, to))))
    case ty => super.Substitution(ty, from, to)
  }


  /* extends isVal */
  override def isVal(t: Term): Boolean = t match {
    case BoolT(_) => true
    case NumT(_) => true
    case RecT(rec) => rec.forall(e => isVal(e._2))
    case t => super.isVal(t)
  }


  /* extends Reduce */
  override def Reduce(t: Term): Term = t match {
    case t if isVal(t) => t
    case If(b, th, e) => b match {
      case BoolT(b) => if (b) th else e
      case b => If(Reduce(b), th, e)
    }
    case Succ(n) => n match {
      case NumT(v) => NumT(v + 1)
      case n => Succ(Reduce(n))
    }
    case RecT(rec) =>
      RecT((rec.keys.toList zip Reduce(rec.values.toList)).toMap)
    case Prj(recT, l) => recT match {
      case RecT(rec) if isVal(recT) => rec(l)
      case recT => Prj(Reduce(recT), l)
    }
    case Let(x, tAssign, tin) =>
      if (isVal(tAssign)) Substitution(tin, Var(x), tAssign)
      else Let(x, Reduce(tAssign), tin)
    case t => super.Reduce(t)
  }

  /* Reduce the List of Term in order */
  def Reduce(l: List[Term]): List[Term] = Reduce(List(), l)

  @tailrec
  private def Reduce(res: List[Term], l: List[Term]): List[Term] = l match {
    case h :: t =>
      if (isVal(h)) Reduce(res :+ h, t)
      else res ++ (Reduce(h) :: t)
    case Nil =>
      println("List alread a value!")
      res
  }


  /* extends Concrete */
  override def Concrete(fc: FirstClass): String = fc match {
    /* Type */
    case Bool => "Bool"
    case Num => "Num"
    case Rec(rec) => rec.foldLeft("{")((s, e) => s + " " + e._1 + "->" + Concrete(e._2)) + " }"

    /* Term */
    case BoolT(b) => if(b) "true" else "false"
    case If(b, th, e) => "if(" + Concrete(b) + "){" + Concrete(th) + "}else{" + Concrete(e) + "}"
    case NumT(n) => n + ""
    case Succ(n) => Concrete(n) + "++"
    case RecT(rec) => rec.foldLeft("{")((s, e) => s + " " + e._1 + "->" + Concrete(e._2)) + " }"
    case Prj(rec, l) => Concrete(rec) + "." + l
    case Let(x, tAssign, tin) => "Let " + x + "=" + Concrete(tAssign) + " in " + Concrete(tin)

    case t => super.Concrete(t)
  }


  println()
  println("<Simple Extension>")
  println()

  /* simple test */
  private val record1 = RecT(Map("a"->NumT(0), "b"->BoolT(true), "c"->Abs("a", Num, Succ(Var("a")))))

  private val test1 = App(Prj(record1, "c"), Prj(record1, "a"))

  Test(test1)

  private val idNumArrow = Abs("x", Arrow(Num, Num), Var("x"))

  private val idBool = Abs("x", Bool, Var("x"))

  private val record2 = RecT(Map("a"->test1, "b"->App(idBool, BoolT(true)), "c"->App(idNumArrow, Abs("a", Num, Succ(Var("a"))))))

  private val test2 = App(Prj(record2, "c"), Prj(record2, "a"))

  Test(test2)

}
