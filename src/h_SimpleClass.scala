import scala.annotation.tailrec

object h_SimpleClass extends App {

  case class wp(sto: Map[Int, Term], t: Term)

  trait Type

  case object TopType extends Type
  
  case object BoolType extends Type

  case object NumType extends Type

  case class ArrType(ty1: Type, ty2: Type) extends Type

  case class RecType(m: Map[String, Type]) extends Type

  case class RefType(t: Type) extends Type

//  case class Source(t: Type) extends Type
//
//  case class Sink(t: Type) extends Type

  trait Term
  
  case object UnitTerm extends Term
  
  case class Bool(b: Boolean) extends Term

  case class Num(n: Int) extends Term

  case class Succ(n: Term) extends Term
  
  case class Let(x: String, t: Term, in: Term) extends Term

  case class Var(x: String) extends Term

  case class Abs(x: String, ty: Type, t: Term) extends Term

  case class App(f: Term, p: Term) extends Term

  case class Rec(m: Map[String, Term]) extends Term

  case class Prj(t: Term, l: String) extends Term

  case class Seq(t1: Term, t2: Term) extends Term

  case class Ref(t: Term) extends Term

  case class Deref(t: Term) extends Term

  case class Assign(l: Term, r: Term) extends Term

  case class Fix(t: Term) extends Term

  trait subTerm extends Term

  case class Addr(p: Int) extends subTerm
  
  def Substitution(t: Term, from: String, to: Term): Term = t match {
    case UnitTerm => UnitTerm
    case Bool(b) => Bool(b)
    case Num(n) => Num(n)
    case Succ(n) => Succ(Substitution(n, from, to))
    case Let(x, t, in) => if (x == from) Let(x, t, in) else Let(x, Substitution(t, from, to), Substitution(in, from, to))
    case Var(x) => if (x == from) to else Var(x)
    case Abs(x, ty, t) => if (x == from) Abs(x, ty, t) else Abs(x, ty, Substitution(t, from, to))
    case App(f, p) => App(Substitution(f, from, to), Substitution(p, from, to))
    case Rec(m) => Rec(m.foldLeft(Map[String, Term]())((m, e) => m + (e._1 -> Substitution(e._2, from, to))))
    case Prj(r, l) => Prj(Substitution(r, from, to), l)
    case Seq(t1, t2) => Seq(Substitution(t1, from, to), Substitution(t2, from, to))
    case Ref(t) => Ref(Substitution(t, from, to))
    case Deref(t) => Deref(Substitution(t, from, to))
    case Assign(l, r) => Assign(Substitution(l, from, to), Substitution(r, from, to))
    case Fix(t) => Fix(Substitution(t, from, to))
    case Addr(p) => Addr(p)
  }

  def SubType(ty1: Type, ty2: Type): Boolean = (ty1, ty2) match {
    case (ty1, ty2) if ty1 == ty2 => true
    case (_, TopType) => true
    case (BoolType, NumType) => true
    case (ArrType(p1, t1), ArrType(p2, t2)) => SubType(p2, p1) && SubType(t1, t2)
    case (RecType(m1), RecType(m2)) => m2.forall(e => m1.get(e._1) match {
      case Some(ty) => SubType(ty, e._2)
      case _ => false
    })
    case (RefType(ty1), RefType(ty2)) => SubType(ty1, ty2)
//    case (Source(ty1), Source(ty2)) => SubType(ty1, ty2)
//    case (Sink(ty1), Sink(ty2)) => SubType(ty2, ty1)
//    case (RefType(ty1), Source(ty2)) if ty1 == ty2 => true
//    case (RefType(ty1), Sink(ty2)) if ty1 == ty2 => true
    case _ => false
  }

  def TypeCheck(t: Term): Type = TypeCheck(Map(), t)
  def TypeCheck(env: Map[String, Type], t: Term): Type = t match {
    case UnitTerm => TopType
    case Bool(_) => BoolType
    case Num(_) => NumType
    case Succ(n) => TypeCheck(env, n) match {
      case NumType => NumType
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\n" + ty + "is not NumType")
    }
    case Let(x, t1, in) => TypeCheck(env + (x -> TypeCheck(env, t1)), in)
    case Var(x) => env.get(x) match {
      case Some(ty) => ty
      case _ => throw new RuntimeException("type check fails at " + Concrete(t) + "\n" + "free variable " + x)
    }
    case Abs(x, ty, t1) => ArrType(ty, TypeCheck(env + (x->ty), t1))
    case App(t1, t2) => TypeCheck(env, t1) match {
      case ArrType(pty, tty) if SubType(TypeCheck(env, t2), pty) => tty
      case ArrType(ty, _) => throw new RuntimeException("type check fails at " + Concrete(t) + "\narrow subtype fail " + TypeCheck(env, t2) + " & " + ty)
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\nincompatible abs " + ty + " & " + TypeCheck(env, t2))
    }
    case Rec(m) => RecType(m.foldLeft(Map[String, Type]())((m, e) => m + (e._1 -> TypeCheck(env, e._2))))
    case Prj(t1, l) => TypeCheck(env, t1) match {
      case RecType(m) if m.contains(l) => m(l)
      case RecType(m) => throw new RuntimeException("type check fails at " + Concrete(t) + "\nno matching " + m + " & " + l )
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\nincompatible rec " + ty + " & " + l )
    }
    case Seq(t1, t2) => TypeCheck(env, t1) match {
      case _ => TypeCheck(env, t2)
      case _ => throw new RuntimeException("type check fails at " + Concrete(t))
    }
    case Ref(t) => RefType(TypeCheck(env, t))
    case Deref(ty) => TypeCheck(env, ty) match {
      case RefType(ty) => ty
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\nnot ref " + ty)
    }
    case Assign(l, r) => TypeCheck(env, l) match {
      case RefType(ty) if SubType(TypeCheck(env, r), ty) => TopType
      case RefType(ty) => throw new RuntimeException("type check fails at " + Concrete(t) + "\nref subtype fail " + TypeCheck(env, r) + " & " + ty)
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\nnot ref" + ty)
    }
    case Fix(t) => TypeCheck(env, t) match {
      case ArrType(_, tty) => tty
      case ty => throw new RuntimeException("type check fails at " + Concrete(t) + "\nincompatible type to fix " + ty)
    }
    case Addr(_) => throw new RuntimeException("type check fails at " + Concrete(t))
  }

  def Concrete(t: Term): String = t match {
    case UnitTerm => "unit"
    case Bool(b) => b + ""
    case Num(n) => "" + n
    case Succ(n) => "Succ(" + Concrete(n) + ")"
    case Let(x, t1, in) => "[Let " + x + " = " + Concrete(t1) + " in" + "\n\t\t" + Concrete(in) + "]"
    case Var(x) => x
    case Abs(x, _, t1) => "(^" + x + ", " + Concrete(t1) + ")"
    case App(t1, t2) => "@(" + Concrete(t1) + " " + Concrete(t2) + ")"
    case Rec(m) => m.foldLeft("{ ")((s, e) => s + e._1 + ": " + Concrete(e._2) + "  ") + "}"
    case Prj(t1, l) => Concrete(t1) + "." + l
    case Seq(t1, t2) => Concrete(t1) + ";" + Concrete(t2)
    case Ref(t1) => "Ref<" + Concrete(t1) + ">"
    case Deref(p) => "!" + Concrete(p)
    case Assign(p, t) => Concrete(p) + ":=" + Concrete(t)
    case Fix(t1) => "Fix(" + Concrete(t1) + ")"
    case Addr(a) => "`" + a + "`"

  }

  @tailrec
  def find_addr(sto: Map[Int, Term], n: Int): Int = if (sto.contains(n)) find_addr(sto, n + 1) else n
  def find_addr(sto: Map[Int, Term]): Int = find_addr(sto, 0)

  def isVal(t: Term): Boolean = t match {
    case UnitTerm => true
    case Bool(_) => true
    case Num(_) => true
    case Abs(_, _, _) => true
    case Rec(m) => m.forall(e => isVal(e._2))
    case Addr(_) => true
    case _ => false
  }

  def mReduce(sto: Map[Int, Term], m: Map[String, Term]): (Map[Int, Term], Map[String, Term]) = {
    val p = mReduce(sto, m.toList, List())
    (p._1, p._2.toMap)
  }
  @tailrec
  def mReduce(sto: Map[Int, Term], m: List[(String, Term)], res: List[(String, Term)]): (Map[Int, Term], List[(String, Term)]) = m match {
    case h :: t => h._2 match {
      case t0 if isVal(t0) => mReduce(sto, t, res :+ h)
      case _ =>
        val wp = Reduce(sto, h._2)
        (wp.sto, res ::: (h._1, wp.t) :: t)
    }
    case Nil => (sto, res)

  }

  def Reduce(sto: Map[Int, Term], t: Term): wp = t match {
    case Succ(n) => n match {
      case Num(n1) => wp(sto, Num(n1 + 1))
      case _ =>
        val w = Reduce(sto, n)
        wp(w.sto, Succ(w.t))
    }
    case Let(x, t, in) => t match {
      case v if isVal(v) => wp(sto, Substitution(in, x, v))
      case _ =>
        val w = Reduce(sto, t)
        wp(w.sto, Let(x, w.t, in))
    }
    case App(f, p) => f match {
      case Abs(x, _, t) if isVal(p) => wp(sto, Substitution(t, x, p))
      case Abs(_, _, _) =>
        val w = Reduce(sto, p)
        wp(w.sto, App(f, w.t))
      case _ =>
        val w = Reduce(sto, f)
        wp(w.sto, App(w.t, p))
    }
    case Seq(t1, t2) => t1 match {
      case UnitTerm => wp(sto, t2)
      case _ =>
        val w = Reduce(sto, t1)
        wp(w.sto, Seq(w.t, t2))
    }
    case Ref(t) => t match {
      case v if isVal(v) =>
        val p = find_addr(sto)
        wp(sto + (p -> v), Addr(p))
      case _ =>
        val w = Reduce(sto, t)
        wp(w.sto, Ref(w.t))
    }
    case Deref(t) => t match {
      case Addr(p) => wp(sto, sto(p))
      case _ =>
        val w = Reduce(sto, t)
        wp(w.sto, Deref(w.t))
    }
    case Assign(l, r) => l match {
      case Addr(p) => r match {
        case v if isVal(v) => wp(sto + (p -> v), UnitTerm)
        case _ =>
          val w = Reduce(sto, r)
          wp(w.sto, Assign(l, w.t))
      }
      case _ =>
        val w = Reduce(sto, l)
        wp(w.sto, Assign(w.t, r))
    }
    case Rec(m) =>
      val p = mReduce(sto, m)
      wp(p._1, Rec(p._2))
    case Prj(r, l) => r match {
      case Rec(m) if isVal(Rec(m)) => wp(sto, m(l))
      case _ =>
        val w = Reduce(sto, r)
        wp(w.sto, Prj(w.t, l))
    }
    case Fix(t1) => t1 match {
      case Abs(x, _, in) => wp(sto, Substitution(in, x, t))
      case _ =>
        val w = Reduce(sto, t1)
        wp(w.sto, Fix(w.t))
    }
    case _ => wp(sto, t)

  }

//  def concrete(ty: Type): String = ty match {
//    case UnitType => "Unit"
//    case NumType => "Num"
//    case AbsType(ty1, ty2) => concrete(ty1) + "->" + concrete(ty2)
//    case RefType(t) => "Ref(" + concrete(t) + ")"
//  }
//

  def FullReduce(t: Term): Term = FullReduce(Map(), t, 0)
  @tailrec
  def FullReduce(sto: Map[Int, Term], t: Term, i: Int): Term = {
//    println("\t" + i + ": " + Concrete(t))
//    println("\t\t sto: " + sto)
    val wp = Reduce(sto, t)
    wp.t match {
      case res if res == t =>
        println("Normal Form:\n\t" + Concrete(res))
        println("sto: " + wp.sto)
        println("total step: " + i)
        res
      case res => FullReduce(wp.sto, res, i + 1)
    }
  }


  def Test(t: Term): Unit = {
    println()
    println(Concrete(t))
    println(TypeCheck(t))
    FullReduce(t)
  }



  //basic class
  val CounterRep = RecType(Map("x"->RefType(NumType)))
  val CounterClass = Abs("r", CounterRep, Rec(Map(
    "get"->Abs("_", TopType, Deref(Prj(Var("r"), "x"))),
    "inc"->Abs("_", TopType, Assign(Prj(Var("r"), "x"), Succ(Deref(Prj(Var("r"), "x")))))
  )))
  val newCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)))), App(CounterClass, Var("r"))))

  val CounterTest = App(newCounter, UnitTerm)
  Test(CounterTest)



  //sub class
  val ResetCounterClass = Abs("r", CounterRep, Let("super", App(CounterClass, Var("r")), Rec(Map(
    "get"->Prj(Var("super"), "get"),
    "inc"->Prj(Var("super"), "inc"),
    "reset"->Abs("_", TopType, Assign(Prj(Var("r"), "x"), Num(1)))
    ))))
  val newResetCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)))), App(ResetCounterClass, Var("r"))))

  val ResetCounterTest = App(newResetCounter, UnitTerm)
  Test(ResetCounterTest)



  //using instance variable
  val BackupCounterRep = RecType(Map("x"->RefType(NumType), "b"->RefType(NumType)))
  val BackupCounterClass = Abs("r", BackupCounterRep, Let("super", App(ResetCounterClass, Var("r")), Rec(Map(
    "get"->Prj(Var("super"), "get"),
    "inc"->Prj(Var("super"), "inc"),
    "reset"->Abs("_", TopType, Assign(Prj(Var("r"), "x"), Deref(Prj(Var("r"), "b")))),
    "backup"->Abs("_", TopType, Assign(Prj(Var("r"), "b"), Deref(Prj(Var("r"), "x"))))
  ))))
  val newBackupCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)), "b"->Ref(Num(1)))), App(BackupCounterClass, Var("r"))))

  val BackupCounterTest = Let("obj", App(newBackupCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "backup"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "reset"), UnitTerm)
    )))))
  Test(BackupCounterTest)



  //open recursion & self (diverging)
  val SetCounter = RecType(Map("get"->ArrType(TopType, NumType), "set"->ArrType(NumType, TopType), "inc"->ArrType(TopType, TopType)))
  var SetCounterClass = Abs("r", CounterRep, Abs("self", SetCounter, Rec(Map(
    "get"->Abs("_", TopType, Deref(Prj(Var("r"), "x"))),
    "set"->Abs("i", NumType, Assign(Prj(Var("r"), "x"), Var("i"))),
    "inc"->Abs("_", TopType, App(Prj(Var("self"), "set"), Succ(App(Prj(Var("self"), "get"), UnitTerm))))
  ))))
  var newSetCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)))), Fix(App(SetCounterClass, Var("r")))))

  var SetCounterTest = Let("obj", App(newSetCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "set"), Num(17)),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "get"), UnitTerm)
    )))))
  Test(SetCounterTest)


  //reference open recursion
  SetCounterClass = Abs("r", CounterRep, Abs("self", ArrType(TopType, SetCounter), Abs("_", TopType, Rec(Map(
    "get"->Abs("_", TopType, Deref(Prj(Var("r"), "x"))),
    "set"->Abs("i", NumType, Assign(Prj(Var("r"), "x"), Var("i"))),
    "inc"->Abs("_", TopType, App(Prj(App(Var("self"), UnitTerm), "set"), Succ(App(Prj(App(Var("self"), UnitTerm), "get"), UnitTerm))))
  )))))
  newSetCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)))), App(Fix(App(SetCounterClass, Var("r"))), UnitTerm)))
  SetCounterTest = Let("obj", App(newSetCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "set"), Num(17)),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "get"), UnitTerm)
    )))))
  Test(SetCounterTest)

  val InstrCounterRep = RecType(Map("x"->RefType(NumType), "a"->RefType(NumType)))
  val InstrCounter = RecType(Map("get"->ArrType(TopType, NumType), "set"->ArrType(NumType, TopType),
                                 "inc"->ArrType(TopType, TopType), "accesses"->ArrType(TopType, NumType)))
  var InstrCounterClass = Abs("r", InstrCounterRep, Abs("self", ArrType(TopType, InstrCounter), Abs("_", TopType,
    Let("super", App(App(App(SetCounterClass, Var("r")), Var("self")), UnitTerm),
      Rec(Map(
      "get"->Prj(Var("super"), "get"),
      "set"->Abs("i", NumType, Seq(Assign(Prj(Var("r"), "a"), Succ(Deref(Prj(Var("r"), "a")))), App(Prj(Var("super"), "set"), Var("i")))),
      "inc"->Prj(Var("super"), "inc"),
      "accesses"->Abs("_", TopType, Deref(Prj(Var("r"), "a")))
      ))))))
  var newInstrCounter = Abs("_", TopType, Let("r", Rec(Map("x"->Ref(Num(1)), "a"->Ref(Num(0)))),
    App(Fix(App(InstrCounterClass, Var("r"))), UnitTerm)))
  var InstrCounterTest = Let("obj", App(newInstrCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "set"), Num(17)),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "accesses"), UnitTerm)
    )))))
  Test(InstrCounterTest)



  //self reference
  val dummySetCounter = Rec(Map(
    "get"->Abs("_", TopType, Num(0)),
    "set"->Abs("i", NumType, UnitTerm),
    "inc"->Abs("_", TopType, UnitTerm)
    ))
  SetCounterClass = Abs("r", CounterRep, Abs("self", RefType(SetCounter), Rec(Map(
    "get"->Abs("_", TopType, Deref(Prj(Var("r"), "x"))),
    "set"->Abs("i", NumType, Assign(Prj(Var("r"), "x"), Var("i"))),
    "inc"->Abs("_", TopType, App(Prj(Deref(Var("self")), "set"), Succ(App(Prj(Deref(Var("self")), "get"), UnitTerm))))
    ))))
  newSetCounter = Abs("_", TopType,
    Let("r", Rec(Map("x"->Ref(Num(1)))),
      Let("cAux", Ref(dummySetCounter),
      Seq(Assign(Var("cAux"), App(App(SetCounterClass, Var("r")), Var("cAux"))), Deref(Var("cAux")))
  )))
  SetCounterTest = Let("obj", App(newSetCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "set"), Num(17)),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "get"), UnitTerm)
    )))))
  Test(SetCounterTest)

  val dummyInstrCounter = Rec(Map(
    "get"->Abs("_", TopType, Num(0)),
    "set"->Abs("i", NumType, UnitTerm),
    "inc"->Abs("_", TopType, UnitTerm),
    "accesses"->Abs("_", TopType, Num(0))
    ))
  InstrCounterClass = Abs("r", InstrCounterRep, Abs("self", RefType(InstrCounter),
    Let("super", App(App(SetCounterClass, Var("r")), Var("self")),
      Rec(Map(
        "get"->Prj(Var("super"), "get"),
        "set"->Abs("i", NumType, Seq(Assign(Prj(Var("r"), "a"), Succ(Deref(Prj(Var("r"), "a")))), App(Prj(Var("super"), "set"), Var("i")))),
        "inc"->Prj(Var("super"), "inc"),
        "accesses"->Abs("_", TopType, Deref(Prj(Var("r"), "a")))
        )))))
  newInstrCounter = Abs("_", TopType,
    Let("r", Rec(Map("x"->Ref(Num(1)), "a"->Ref(Num(0)))),
      Let("cAux", Ref(dummyInstrCounter),
        Seq(Assign(Var("cAux"), App(App(InstrCounterClass, Var("r")), Var("cAux"))), Deref(Var("cAux")))
  )))
  InstrCounterTest = Let("obj", App(newInstrCounter, UnitTerm),
    Seq(App(Prj(Var("obj"), "set"), Num(17)),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
    Seq(App(Prj(Var("obj"), "inc"), UnitTerm),
        App(Prj(Var("obj"), "accesses"), UnitTerm)
          )))))
  Test(InstrCounterTest)
}
