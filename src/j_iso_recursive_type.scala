import scala.annotation.tailrec

object j_iso_recursive_type extends App {

  trait Type

  case object Top extends Type

  case object Nat extends Type

  case class Arrow(f: Type, b: Type) extends Type

  case class Record(m: Map[String, Type]) extends Type

  case class Variant(m: Map[String, Type]) extends Type

  case class uVar(x: String) extends Type

  case class uRec(x: String, ty: Type) extends Type


  trait Term

  case object UnitTerm extends Term

  case class Num(n: Int) extends Term

  case class Var(x: String) extends Term

  case class Abs(x: String, ty: Type, t: Term) extends Term

  case class App(f: Term, p: Term) extends Term

  case class Rec(m: Map[String, Term]) extends Term

  case class Prj(t: Term, l: String) extends Term

  case class Tag(x: String, t: Term, ty: Variant) extends Term

  case class Case(t: Term, m: Map[String, (String, Term)]) extends Term

  case class Fold(ty: Type, t: Term) extends Term

  case class Unfold(ty: Type, t: Term) extends Term



  def lSubstitution(l: List[Type], from: String, to: Type): List[Type] =
    l.foldRight(List[Type]())((e, res) => Substitution(e, from, to) :: res)

  def mSubstitution(m: Map[String, Type], from: String, to: Type): Map[String, Type] = {
    val keys = m.keys.toList
    val values = lSubstitution(m.values.toList, from, to)
    (keys zip values).toMap
  }

  def Substitution(ty: Type, from: String, to: Type): Type = ty match {
    case Arrow(f, b) => Arrow(Substitution(f, from, to), Substitution(b, from, to))
    case Record(m) => Record(mSubstitution(m, from, to))
    case Variant(m) => Variant(mSubstitution(m, from, to))
    case uVar(x) => if (x == from) to else uVar(x)
    case uRec(x, ty) => uRec(x, Substitution(ty, from, to))//??
    case ty => ty
  }


  def CaseType(env: Map[String, Type], c: (String, Term), v: Type): Type = TypeCheck(env + (c._1 -> v), c._2)

  def CaseTypeCheck(env: Map[String, Type], cm: Map[String, (String, Term)], vm: Map[String, Type]): Type =
    CaseTypeCheck(env, cm.tail, vm.tail.toList, CaseType(env, cm.head._2, vm.head._2))

  @tailrec
  def CaseTypeCheck(env: Map[String, Type], cm: Map[String, (String, Term)], vm: List[(String, Type)], expected: Type): Type = vm match {
    case h :: t => cm.get(h._1) match {
      case Some(c) => CaseType(env, c, h._2) match {
        case ty if ty == expected => CaseTypeCheck(env, cm, t, expected)
        case ty => throw new RuntimeException("Incompatible Type, Expected " + expected + " Actual " + ty)
      }
      case None => throw new RuntimeException("No Such Case " + h._1)
    }
    case Nil => expected
  }

  def lTypeCheck(env: Map[String, Type], l: List[Term]): List[Type] =
    l.foldRight(List[Type]())((e, res) => TypeCheck(env, e) :: res)

  def mTypeCheck(env: Map[String, Type], m: Map[String, Term]): Map[String, Type] = {
    val keys = m.keys.toList
    val values = lTypeCheck(env, m.values.toList)
    (keys zip values).toMap
  }

  def TypeCheck(t: Term): Type = TypeCheck(Map(), t)

  def TypeCheck(env: Map[String, Type], t: Term): Type = t match {
    case UnitTerm => Top
    case Num(_) => Nat
    case Var(x) => env.get(x) match {
      case Some(v) => v
      case None => throw new RuntimeException("Free Variable " + x)
    }
    case Abs(x, ty, t0) => Arrow(ty, TypeCheck(env + (x->ty), t0))
    case App(t1, t2) => TypeCheck(env, t1) match {
      case Arrow(f, b) => TypeCheck(env, t2) match {
        case ty if ty == f => b
        case ty => throw new RuntimeException("Incompatible Type, Applying" + Arrow(f, b) + " to " + ty)
      }
      case ty => throw new RuntimeException("Incompatible Type, Applying" + ty)
    }
    case Rec(m) => Record(mTypeCheck(env, m))
    case Prj(t0, l) => TypeCheck(env, t0) match {
      case Record(m) => m.get(l) match {
        case Some(ty) => ty
        case None => throw new RuntimeException("No Such Lable " + l)
      }
      case ty => throw new RuntimeException("Incompatible Type, Projecting " + ty)
    }
    case Tag(_, _, ty) => ty
    case Case(t0, m) => TypeCheck(env, t0) match {
      case Variant(v) => CaseTypeCheck(env, m, v)
      case ty => throw new RuntimeException("Incompatible Type, Case to" + ty)
    }
    case Fold(u, t0) => u match {
      case uRec(x, rty) => TypeCheck(env, t0) match {
        case ty if ty == Substitution(rty, x, u) => u
        case ty => throw new RuntimeException("Incompatible Type Expected " + u + " Actual " + ty)
      }
      case ty => throw new RuntimeException("Incompatible Type to Fold " + ty)
    }
    case Unfold(u, t0) => u match {
      case uRec(x, rty) => TypeCheck(env, t0) match {
        case ty if ty == u => Substitution(rty, x, u)
        case ty => throw new RuntimeException("Incompatible Type Expected " + u + " Actual " + ty)
      }
      case ty => throw new RuntimeException("Incompatible Type to Unfold " + ty)
    }
  }



  def isVal(l: List[Term]): Boolean = l.forall(isVal)

  def isVal(m: Map[String, Term]): Boolean = m.values.forall(isVal)

  def isVal(t: Term): Boolean = t match {
    case UnitTerm => true
    case Num(_) => true
    case Abs(_, _, _) => true
    case Rec(m) if isVal(m) => true
    case Fold(_, t0) if isVal(t0) => true
    case _ => false
  }


  def lSubstitution(l: List[Term], from: String, to: Term): List[Term] =
    l.foldRight(List[Term]())((e, res) => Substitution(e, from, to) :: res)

  def mSubstitution(m: Map[String, Term], from: String, to: Term): Map[String, Term] = {
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

  def Substitution(t: Term, from: String, to: Term): Term = t match {
    case Var(x) => if (x == from) to else Var(x)
    case Abs(x, ty, t) => if (x == from) Abs(x, ty, t) else Abs(x, ty, Substitution(t, from, to))
    case App(f, p) => App(Substitution(f, from, to), Substitution(p, from, to))
    case Rec(m) => Rec(mSubstitution(m, from, to))
    case Prj(t0, l) => Prj(Substitution(t0, from, to), l)
    case Tag(x, t0, ty) => Tag(x, Substitution(t0, from, to), ty)
    case Case(t0, m) => Case(Substitution(t0, from, to), cSubstitution(m, from, to))
    case Fold(ty, t0) => Fold(ty, Substitution(t0, from, to))
    case Unfold(ty, t0) => Unfold(ty, Substitution(t0, from, to))
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
    case App(f, p) => (f, p) match {
      case (Abs(x, _, t0), p) if isVal(p) => Substitution(t0, x, p)
      case (f, _) if isVal(f) => App(f, Reduce(p))
      case _ => App(Reduce(f), p)
    }
    case Rec(m) => Rec(mReduce(m))
    case Prj(t0, l) => t0 match {
      case Rec(m) if isVal(t0) => m(l)
      case _ => Prj(Reduce(t0), l)
    }
    case Tag(x, t0, ty) => if (isVal(t0)) t0 else Tag(x, Reduce(t0), ty)
    case Case(t0, m) => t0 match {
      case Tag(x, t1, _) if isVal(t1) =>
        val c = m(x)
        Substitution(c._2, c._1, t1)
      case _ => Case(Reduce(t0), m)
    }
    case Fold(u, t0) => Fold(u, Reduce(t0))
    case Unfold(u, t0) => t0 match {
      case Fold(_, t1) if isVal(t1) => t1
      case _ => Unfold(u, Reduce(t0))
    }
    case _ => t
  }


  def FullReduce(t: Term): Term = FullReduce(t, 0)

  @tailrec
  def FullReduce(t: Term, i: Int): Term = {
    println("\t" + i + ": " + t)
    Reduce(t) match {
      case res if res == t => res
      case res => FullReduce(res, i + 1)
    }
  }

  def Test(t: Term): Unit = {
    println(t)
    println(TypeCheck(t))
    FullReduce(t)
    println()
  }


  val NatList = uRec("X", Variant(Map("nil"->Top, "cons"->Record(Map("1"->Nat, "2"->uVar("X"))))))
  val NatListType = Substitution(NatList.ty, NatList.x, NatList) match {case Variant(m) => Variant(m)}

  def nil(): Term = Fold(NatList, Tag("nil", UnitTerm, NatListType))
  def cons(): Term = Abs("n", Nat, Abs("l", NatList, Fold(NatList, Tag("cons", Rec(Map("1"->Var("n"), "2"->Var("l"))), NatListType))))

//  Test(nil())
  Test(App(App(cons(), Num(1)), App(App(cons(), Num(2)), nil())))




}

