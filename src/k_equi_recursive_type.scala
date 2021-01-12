import scala.annotation.tailrec

object k_equi_recursive_type extends App{

  /* Type */
  trait Type

  case object Top extends Type

  case object Nat extends Type

  case object Even extends Type

  case class Arrow(f: Type, b: Type) extends Type

  case class Record(m: Map[String, Type]) extends Type

  case class Variant(m: Map[String, Type]) extends Type

  case class uVar(x: String) extends Type

  case class uRec[T <: Type](x: String, ty: T) extends Type


  /* Term */
  trait Term

  case object UnitTerm extends Term

  case class Num(n: Int) extends Term

  case class EvenNum(n: Int) extends Term

  case class Var(x: String) extends Term

  case class Abs(x: String, ty: Type, t: Term) extends Term

  case class App(f: Term, p: Term) extends Term

  case class Pred(n: Term) extends Term

  case class Mult(n: Term, m: Term) extends Term

  case class If(b: Term, t: Term, e: Term) extends Term

  case class Rec(m: Map[String, Term]) extends Term

  case class Prj(t: Term, l: String) extends Term

  case class Tag(x: String, t: Term, ty: Variant) extends Term

  case class Case(t: Term, m: Map[String, (String, Term)]) extends Term


  /* Type Substitution helper function */

  /* It substitutes the List of Types  */
  def lSubstitution(l: List[Type], from: String, to: Type): List[Type] =
    l.foldRight(List[Type]())((e, res) => Substitution(e, from, to) :: res)

  /* It substitutes the Map of Types. Any Key type (scala) can be used. */
  def mSubstitution[Key](m: Map[Key, Type], from: String, to: Type): Map[Key, Type] = {
    val keys = m.keys.toList
    val values = lSubstitution(m.values.toList, from, to)
    (keys zip values).toMap
  }

  /* Type Substitution for Recursive Type! */
  def Substitution[T <: Type](ty: T, from: String, to: Type): T = ty match {
    case Arrow(f, b) => Arrow(Substitution(f, from, to), Substitution(b, from, to)).asInstanceOf[T]
    case Record(m) => Record(mSubstitution(m, from, to)).asInstanceOf[T]
    case Variant(m) => Variant(mSubstitution(m, from, to)).asInstanceOf[T]
    case uVar(x) => if (x == from) to.asInstanceOf[T] else uVar(x).asInstanceOf[T]
    case uRec(x, ty) =>
      if (x != from) uRec(x, Substitution(ty, from, to)).asInstanceOf[T]
      else uRec(x, ty).asInstanceOf[T]
    case ty => ty
  }


  /* Unfold the uRec */
  @tailrec
  def Unfold(ty: Type): Type = ty match {
    case uRec(x1, ty1) => Unfold(Substitution(ty1, x1, ty))
    case ty => ty
  }



  def recordSubtype[Key](A: Set[(Type, Type)], m1: Map[Key, Type], m2: Map[Key, Type]): Set[(Type, Type)] =
    recordSubtype(A, m1, m2.toList)

  @tailrec
  def recordSubtype[Key](A: Set[(Type, Type)], m1: Map[Key, Type],
                         m2: List[(Key, Type)]): Set[(Type, Type)] = m2 match {
    case h :: t => m1.get(h._1) match {
      case Some(v) =>
        val A1 = Subtype(A, v, h._2)
        if (A1.isEmpty) A1
        else recordSubtype(A1, m1, t)
      case None => Set()
    }
    case Nil => A
  }

  /* It checks the subtype relation between ty1 and ty2 */
  def Subtype(s: Type, t: Type): Boolean = Subtype(Set(), s, t).nonEmpty

  /* Subtyping algorithm */
  def Subtype(A: Set[(Type, Type)], s: Type, t: Type): Set[(Type, Type)] = {
    if (A.contains(s, t)) A
    else {
      val A0 = A + (s->t)
      (s, t) match {
        case _ if s == t => A0
        case (_, Top) => A0
        case (Even, Nat) => A0
        case (Arrow(s1, s2), Arrow(t1, t2)) =>
          val A1 = Subtype(A0, t1, s1)
          if (A1.isEmpty) A1
          else Subtype(A1, s2, t2)
        case (Record(m1), Record(m2)) => recordSubtype(A0, m1, m2)
        case (s, uRec(x, ty)) => Subtype(A0, s, Substitution(ty, x, uRec(x, ty)))
        case (uRec(x, ty), t) => Subtype(A0, Substitution(ty, x, uRec(x, ty)), t)
        case _ => Set()
      }
    }
  }

  /* TypeCheck helper functions */

  /* It checks the Case Term. */
  def CaseType(env: Map[String, Type], c: (String, Term), v: Type): Type = TypeCheck(env + (c._1 -> v), c._2)

  def CaseTypeCheck(env: Map[String, Type], cm: Map[String, (String, Term)], vm: Map[String, Type]): Type =
    CaseTypeCheck(env, cm.tail, vm.tail.toList, CaseType(env, cm.head._2, vm.head._2))

  @tailrec
  def CaseTypeCheck(env: Map[String, Type], cm: Map[String, (String, Term)], vm: List[(String, Type)],
                    expected: Type): Type = vm match {
    case h :: t => cm.get(h._1) match {
      case Some(c) => CaseType(env, c, h._2) match {
        case ty if ty == expected => CaseTypeCheck(env, cm, t, expected)
        case ty => throw new RuntimeException("Case, Expected " + expected + " Actual " + ty)
      }
      case None => throw new RuntimeException("No Such Case " + h._1)
    }
    case Nil => expected
  }

  /* It checks the Type of the List of Terms */
  def lTypeCheck(env: Map[String, Type], l: List[Term]): List[Type] =
    l.foldRight(List[Type]())((e, res) => TypeCheck(env, e) :: res)

  /* It checks the Type of the Map of Terms */
  def mTypeCheck[Key](env: Map[String, Type], m: Map[Key, Term]): Map[Key, Type] = {
    val keys = m.keys.toList
    val values = lTypeCheck(env, m.values.toList)
    (keys zip values).toMap
  }

  /* It checks the Type of the Term t. If Type Checking fails, if throw exception.
     If succeed, it returns the Type of t */
  def TypeCheck(t: Term): Type = TypeCheck(Map(), t)

  def TypeCheck(env: Map[String, Type], t: Term): Type = t match {
    case UnitTerm => Top
    case EvenNum(_) => Even
    case Num(_) => Nat
    case Var(x) => env.get(x) match {
      case Some(v) => v
      case None => throw new RuntimeException("Free Variable " + x + " in " + Concrete(t))
    }
    case Abs(x, ty, t0) => Arrow(ty, TypeCheck(env + (x -> ty), t0))
    case App(t1, t2) => Unfold(TypeCheck(env, t1)) match {
      case Arrow(f, b) => TypeCheck(env, t2) match {
        case ty if Subtype(ty, f) => b
        case ty => throw new RuntimeException("Param Expected: " + Concrete(f) +
          " Actual: " + Concrete(ty) + " in " + Concrete(t))
      }
      case ty => throw new RuntimeException("Not a Func: " + ty + " in " + Concrete(t))
    }
    case Pred(n) => Unfold(TypeCheck(env, n)) match {
      case Nat => Nat
      case _ => throw new RuntimeException("Not a Nat " + Concrete(t))
    }
    case Mult(n, m) => (Unfold(TypeCheck(env, n)), Unfold(TypeCheck(env, m))) match {
      case (Nat, Nat) => Nat
      case _ => throw new RuntimeException("Not a Nat " + Concrete(t))
    }
    case If(b, th, e) => Unfold(TypeCheck(env, b)) match {
      case Nat =>
        val thty = TypeCheck(env, th)
        val ety = TypeCheck(env, e)
        if (Subtype(thty, ety)) ety
        else if (Subtype(ety, thty)) thty
        else throw new RuntimeException("If, then: " + Concrete(thty) + " elee: " + Concrete(e))
      case _ => throw new RuntimeException("Not a Nat " + Concrete(t))
    }
    case Rec(m) => Record(mTypeCheck(env, m))
    case Prj(t0, l) => Unfold(TypeCheck(env, t0)) match {
      case Record(m) => m.get(l) match {
        case Some(ty) => ty
        case None => throw new RuntimeException("No Such Lable " + l + " in " + Concrete(t))
      }
      case ty => throw new RuntimeException("Not a Record: " + ty + " in " + Concrete(t))
    }
    case Tag(x, t0, ty) => ty.m.get(x) match {
      case Some(vty) =>
        if (Subtype(TypeCheck(env, t0), vty)) ty
        else throw new RuntimeException("Tag, Expected: " + Concrete(vty) +
          " Actual " + Concrete(TypeCheck(env, t0)) + " in " + Concrete(t))
      case None => throw new RuntimeException("No Such Tag " + x + " in " + Concrete(ty) + " in " + Concrete(t))
    }
    case Case(t0, m) => Unfold(TypeCheck(env, t0)) match {
      case Variant(v) => CaseTypeCheck(env, m, v)
      case ty => throw new RuntimeException("Not a Variant: " + ty + " in " + Concrete(t))
    }
  }


  def isVal(l: List[Term]): Boolean = l.forall(isVal)

  def isVal[Key](m: Map[Key, Term]): Boolean = m.values.forall(isVal)

  def isVal(t: Term): Boolean = t match {
    case UnitTerm => true
    case EvenNum(_) => true
    case Num(_) => true
    case Abs(_, _, _) => true
    case Rec(m) if isVal(m) => true
    case Tag(_, t0, _) if isVal(t0) => true
    case _ => false
  }


  def lSubstitution(l: List[Term], from: String, to: Term): List[Term] =
    l.foldRight(List[Term]())((e, res) => Substitution(e, from, to) :: res)

  def mSubstitution[Key](m: Map[Key, Term], from: String, to: Term): Map[Key, Term] = {
    val keys = m.keys.toList
    val values = lSubstitution(m.values.toList, from, to)
    (keys zip values).toMap
  }

  def cSubstitution(c: Map[String, (String, Term)], from: String, to: Term): Map[String, (String, Term)] = {
    val keys = c.keys.toList
    val m = c.values.toMap
    val caseVars = m.keys.toList
    val caseTerms = lSubstitution(m.values.toList, from, to)
    val values = caseVars zip caseTerms
    (keys zip values).toMap
  }

  def Substitution[T <: Term](t: T, from: String, to: Term): T = t match {
    case Var(x) => if (x == from) to.asInstanceOf[T] else Var(x).asInstanceOf[T]
    case Abs(x, ty, t) =>
      if (x == from) Abs(x, ty, t).asInstanceOf[T]
      else Abs(x, ty, Substitution(t, from, to)).asInstanceOf[T]
    case App(f, p) => App(Substitution(f, from, to), Substitution(p, from, to)).asInstanceOf[T]
    case Pred(n) => Pred(Substitution(n, from, to)).asInstanceOf[T]
    case Mult(n, m) => Mult(Substitution(n, from, to), Substitution(m, from, to)).asInstanceOf[T]
    case If(b, th, e) =>
      If(Substitution(b, from, to),Substitution(th, from, to), Substitution(e, from, to)).asInstanceOf[T]
    case Rec(m) => Rec(mSubstitution(m, from, to)).asInstanceOf[T]
    case Prj(t0, l) => Prj(Substitution(t0, from, to), l).asInstanceOf[T]
    case Tag(x, t0, ty) => Tag(x, Substitution(t0, from, to), ty).asInstanceOf[T]
    case Case(t0, m) => Case(Substitution(t0, from, to), cSubstitution(m, from, to)).asInstanceOf[T]
    case t => t
  }


  def lReduce(l: List[Term]): List[Term] = lReduce(l, List())

  @tailrec
  def lReduce(l: List[Term], res: List[Term]): List[Term] = l match {
    case h :: t if isVal(h) => lReduce(t, res :+ h)
    case h :: t => res ::: Reduce(h) :: t
    case Nil =>
      println("ERROR: All values already!")
      res
  }

  def mReduce(m: Map[String, Term]): Map[String, Term] = {
    val keys = m.keys.toList
    val values = lReduce(m.values.toList)
    (keys zip values).toMap
  }




  def Reduce(t: Term): Term = t match {
    case _ if isVal(t) => t
    case Var("x") => t
    case App(f, p) => (f, p) match {
      case (Abs(x, _, t0), p) if isVal(p) => Substitution(t0, x, p)
      case (f, _) if isVal(f) => App(f, Reduce(p))
      case _ => App(Reduce(f), p)
    }
    case Pred(n) => n match {
      case Num(v) => Num(v - 1)
      case _ => Pred(Reduce(n))
    }
    case Mult(n, m) => (n, m) match {
      case (Num(n1), Num(m1)) => Num(n1 * m1)
      case (n, m) if isVal(n) => Mult(n, Reduce(m))
      case _ => Mult(Reduce(n), m)
    }
    case If(b, th, e) =>
      if (isVal(b)) b match {
        case Num(0) => e
        case _ => th
      }
      else If(Reduce(b), th, e)
    case Rec(m) => Rec(mReduce(m))
    case Prj(t0, l) => t0 match {
      case Rec(m) if isVal(t0) => m(l)
      case _ => Prj(Reduce(t0), l)
    }
    case Tag(x, t0, ty) => Tag(x, Reduce(t0), ty)
    case Case(t0, m) => t0 match {
      case Tag(x, t1, _) if isVal(t1) =>
        val c = m(x)
        Substitution(c._2, c._1, t1)
      case _ => Case(Reduce(t0), m)
    }
    case _ => throw new RuntimeException("Match Error: " + Concrete(t))
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
    println(Concrete(TypeCheck(t)))
    FullReduce(t)
    println()
  }




  /* this function translate Term into readable string */
  def Concrete(t: Term): String = t match {
    case UnitTerm => "Unit"
    case Num(n) => n + ""
    case EvenNum(n) => n + ""
    case Var(x) => x
    case Abs(x, ty, t) => "{^" + x + ":" + Concrete(ty) + "." + Concrete(t) + "}"
    case App(f, p) => "(" + Concrete(f) + " " + Concrete(p) + ")"
    case Pred(n) => Concrete(n) + "'"
    case Mult(n, m) =>Concrete(n) + " * " + Concrete(m)
    case If(b, th, e) => "if (" + Concrete(b) + ")" + " " + Concrete(th) + " else " + Concrete(e)
    case Rec(m) => m.foldLeft("{ ")((s, e) => s + e._1 + "->" + Concrete(e._2) + " ") + "}"
    case Prj(t1, l) => Concrete(t1) + "." + l
    case Tag(x, t, ty) => "<" + x + ":" + Concrete(t) + "> as " + Concrete(ty)
    case Case(t, m) => "case (" + Concrete(t) + ") of " +
      m.foldLeft("")((s, e) => s + "  " + e._1 + ": " + e._2._1 + " -> " + Concrete(e._2._2) + ";")
  }

  /* this function translate Type into readable string */
  def Concrete(t: Type): String = t match {
    case Top => "Top"
    case Nat => "Nat"
    case Even => "Even"
    case Arrow(f, p) => "(" + Concrete(f) + "->" + Concrete(p) + ")"
    case Record(m) => m.foldLeft("{ ")((s, e) => s + e._1 + "->" + Concrete(e._2) + " ") + "}"
    case Variant(m) => m.foldLeft("< ")((s, e) => s + e._1 + ":" + Concrete(e._2) + " ") + ">"
    case uRec(x, ty) => "{u" + x + "." + Concrete(ty) + "}"
    case uVar(x) => x
  }



  /* Recursive Subtype */

  val n2ex = uRec("X", Arrow(Nat, Record(Map("n"->Even, "x"->uVar("X")))))
  val unfold = Substitution(n2ex.ty, "X", n2ex)
  val e2nx = uRec("X", Arrow(Even, Record(Map("n"->Nat, "x"->uVar("X")))))

  println("n2ex: " + Concrete(n2ex))
  println("unfold: " + Concrete(unfold))
  println(Subtype(n2ex, unfold))
  println(Subtype(unfold, n2ex))

  println("n2ex: " + Concrete(n2ex))
  println("e2nx: " + Concrete(e2nx))
  println(Subtype(n2ex, e2nx))
  println(Subtype(e2nx, n2ex))


  /* Simple Recursive Type */
  val NatList = uRec("X", Variant(Map("Nil"->Top, "Cons"->Record(Map("1"-> Nat, "2"->uVar("X"))))))
  val NatListType = Substitution(NatList.ty, "X", NatList)

  def nil(): Term = Tag("Nil", UnitTerm, NatListType)

  def cons(): Term = Abs("n", Nat, Abs("l", NatList, Tag("Cons", Rec(Map("1"->Var("n"), "2"->Var("l"))), NatListType)))

  val list1 = App(App(cons(), Num(1)), App(App(cons(), Num(2)), nil()))

  Test(list1)

  def isNil(): Term = Abs("l", NatList, Case(Var("l"), Map("Nil"->("u", Num(1)), "Cons"->("p", Num(0)))))

  Test(App(isNil(), list1))


  /* Fix
   * We've implemented fix in untyped lambda calculus, but it is hard to describe it with typed lambda calculus.
   * However by using "Recursive Type", it perfectly describes the type of Fix */

  def Fix(t: Term): Term = App(Fix(TypeCheck(t).asInstanceOf[Arrow]), t)
  def Fix(arr: Arrow): Term = Abs("f", arr,
    App(Abs("x", uRec("A", Arrow(uVar("A"), arr.b)), App(Var("f"), Abs("y", arr.b.asInstanceOf[Arrow].b, App(App(Var("x"), Var("x")), Var("y"))))),
        Abs("x", uRec("A", Arrow(uVar("A"), arr.b)), App(Var("f"), Abs("y", arr.b.asInstanceOf[Arrow].b, App(App(Var("x"), Var("x")), Var("y")))))))

  val factorial = Abs("f", Arrow(Nat, Nat), Abs("n", Nat, If(Var("n"),
    Mult(App(Var("f"), Pred(Var("n"))), Var("n")), Num(1))))
  println(Concrete(TypeCheck(factorial)))

  Test(App(Fix(factorial), Num(0)))
  Test(App(Fix(factorial), Num(15)))

}



