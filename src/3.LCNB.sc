//add num & bool

import scala.annotation.tailrec

trait term

case class Var(x: String) extends term

case class Fun(x: String, t: term) extends term

case class FunStep1(x:String, t:term) extends term

case class App(f: term, t: term) extends term

case class AppStep1(f: term, t: term) extends term

case class AppStep2(f: term, t: term) extends term

case object True extends term

case object False extends term

case class Num(n: Int) extends term

case class Op(op: String, l: List[term]) extends term

case object Wrong extends term

/* features */

//default

def Id(): term = Fun("x", Var("x"))

//boolean

def LCTrue(): term = Fun("t", Fun("f", Var("t")))
def LCFalse(): term = Fun("t", Fun("f", Var("f")))
def LCIf(): term = Fun("c", Fun("t", Fun("f", App(App(Var("c"), Var("t")), Var("f")))))

//boolean operation

def And(): term = Fun("a", Fun("b", App(App(Var("a"), Var("b")), LCFalse())))
def Or(): term = Fun("a", Fun("b", App(App(Var("a"), LCTrue()), Var("b"))))
def Not(): term = Fun("a", App(App(App(LCIf(), Var("a")), LCFalse()), LCTrue()))

//pair

def Pair(): term = Fun("a", Fun("b", Fun("s", App(App(Var("s"), Var("b")), Var("a")))))
def First(): term = Fun("p", App(Var("p"), LCFalse()))
def Second(): term = Fun("p", App(Var("p"), LCTrue()))

//church numeral

@tailrec
def Church_helper(n:Int, t:term):term = n match {
  case 0 => t
  case _ => Church_helper(n - 1, App(Var("s"), t))
}
def Church(n:Int):term = Fun("s", Fun("z", Church_helper(n, Var("z"))))
def Succ(): term = Fun("n", Fun("s", Fun("z", App(Var("s"), App(App(Var("n"), Var("s")), Var("z"))))))
def Plus(): term = Fun("m", Fun("n", Fun("s", Fun("z", App(App(Var("m"), Var("s")), App(App(Var("n"), Var("s")), Var("z")))))))
def Mult(): term = Fun("m", Fun("n", App(App(Var("m"), App(Plus(), Var("n"))), Church(0))))
def Power(): term = Fun("m", Fun("n", App(App(Var("n"), App(Mult(), Var("m"))), Church(1))))
def IsZero(): term = Fun("m", App(App(Var("m"),Fun("x", LCFalse())), LCTrue()))
def ZeroPair(): term = App(App(Pair(), Church(0)), Church(0))
def SuccPair(): term = Fun("p", App(App(Pair(), App(Second(), Var("p"))), App(Succ(), App(Second(), Var("p")))))
def Pred(): term = Fun("m", App(First(), App(App(Var("m"), SuccPair()), ZeroPair())))
def Sub(): term = Fun("m", Fun("n", App(App(Var("n"), Pred()), Var("m"))))
def Equal(): term = Fun("m", Fun("n", App(App(And(), App(IsZero(), App(App(Sub(), Var("m")), Var("n")))), App(IsZero(), App(App(Sub(), Var("n")), Var("m"))))))

//list

def EmptyList(): term = Fun("c", Fun("n", Var("n")))
def Cons(): term = Fun("e", Fun("l", Fun("c", Fun("n", App(App(Var("c"), Var("e")), App(App(Var("l"), Var("c")), Var("n")))))))
def Head(): term = Fun("l", App(App(Var("l"), LCTrue()), EmptyList()))
def AlwaysLCFalse(): term = Fun("c", Fun("n", LCFalse()))
def IsNil(): term = Fun("l", App(App(Var("l"), AlwaysLCFalse()), LCTrue()))
def EmptyPair(): term = App(App(Pair(), EmptyList()), EmptyList())
def ConsPair(): term = Fun("e", Fun("p", App(App(Pair(), App(Second(), Var("p"))), App(App(Cons(), Var("e")), App(Second(), Var("p"))))))
def PopFront(): term = Fun("l", App(First(), App(App(Var("l"), ConsPair()), EmptyPair())))
def ConsTail(): term = Fun("e", Fun("l", App(App(App(LCIf(), App(IsNil(), Var("l"))), App(App(Cons(), Var("e")), EmptyList())), Var("l"))))
def Tail(): term = Fun("l", App(App(App(App(Var("l"), ConsTail()), EmptyList()), LCTrue()), EmptyList()))

//real value operations

def If(c: term, t: term, e: term): term  = c match {
  case True => t
  case False => e
  case _ =>
    val l = List(c, t, e)
    Op("if", l)
}

def Eq(m: term, n: term): term = (m, n) match {
  case (Num(m), Num(n)) => if (m == n) True else False
  case _ =>
  val l = List(m, n)
    Op("eq", l)
}

//conversion between term and real value

def ch2bo(t: term): term = App(App(t, True), False)

def bo2ch(b: term): term = b match {
  case True => LCTrue()
  case False => LCFalse()
  case _ => Wrong
}

//recursion

def Diverge(): term = Fun("x", App(Var("x"), Var("x")))
def Fix(): term = Fun("f", App(Fun("x", App(Var("f"), Fun("y", App(App(Var("x"), Var("x")), Var("y"))))), Fun("x", App(Var("f"), Fun("y", App(App(Var("x"), Var("x")), Var("y")))))))

/* evaluation helper functions */

//find free variables

def FV(t: term): Set[String] = {
  def FV_helper(s:Set[String], t:term):Set[String] = {
    @tailrec
    def list_FV(s: Set[String], l: List[term]): Set[String] = l match {
      case h :: t => list_FV(FV_helper(s, h), t)
      case _ => s
    }

    t match {
      case Var(x) => s + x
      case Fun(_, t1) => FV_helper(s, t1)
      case FunStep1(_, t1) => FV_helper(s, t1)
      case App(f, t) =>
        val s1 = FV_helper(s, f)
        FV_helper(s1, t)
      case AppStep1(f, t) =>
        val s1 = FV_helper(s, f)
        FV_helper(s1, t)
      case AppStep2(f, t) =>
        val s1 = FV_helper(s, f)
        FV_helper(s1, t)
      case op:Op => list_FV(s, op.l)
      case _ => s
    }
  }

  FV_helper(Set[String](), t)
}

//find binding variable

def BV(t: term): Set[String] = {
  def BV_helper(s: Set[String], t: term): Set[String] = {
    @tailrec
    def list_BV(s: Set[String], l: List[term]): Set[String] = l match {
      case h :: t => list_BV(BV_helper(s, h), t)
      case _ => s
    }

    t match {
      case Fun(x, t) => BV_helper(s + x, t)
      case FunStep1(x, t) => BV_helper(s + x, t)
      case App(f, t) =>
        val s1 = BV_helper(s, f)
        BV_helper(s1, t)
      case AppStep1(f, t) =>
        val s1 = BV_helper(s, f)
        BV_helper(s1, t)
      case AppStep2(f, t) =>
        val s1 = BV_helper(s, f)
        BV_helper(s1, t)
      case op:Op => list_BV(s, op.l)
      case _ => s
    }
  }

  BV_helper(Set[String](), t)
}

//make replacing string

@tailrec
def find_to(bv: Set[String], fv: Set[String], from: String): String = {
  def mk_to(from: String): String = {
    def mk_to_helper(from: List[Char], carry: Int):List[Char] = from match {
      case a :: b =>
        if (a.isDigit) {
          val num = a.toInt - 48 + carry
          if (num != 9) (num + 49).toChar :: b
          else 48.toChar :: mk_to_helper(b, 1)
        }
        else a :: mk_to_helper(b, 0)
      case _ => '1' :: Nil
    }

    mk_to_helper(from.toList, 0).mkString("")
  }

  if ((bv++fv).contains(from)) find_to(bv, fv, mk_to(from))
  else from
}

//rename from "from" to "to"

def do_rename(t: term, from: String, to: String): term = {
  def list_rename(l: List[term], from: String, to: String): List[term] = {
    @tailrec
    def list_rename_helper(l: List[term], res: List[term], from: String, to: String): List[term] = l match {
      case h :: t =>
        list_rename_helper(t, res :+ do_rename(h, from, to), from, to)
      case _ => res
    }

    list_rename_helper(l, Nil, from, to)
  }

  t match {
    case Var(x) if x == from => Var(to)
    case Fun(x, t1) =>
      if (x == from) Fun(to, do_rename(t1, from, to))
      else Fun(x, do_rename(t1, from, to))
    case FunStep1(x, t1) =>
      if (x == from) FunStep1(to, do_rename(t1, from, to))
      else FunStep1(x, do_rename(t1, from, to))
    case App(f, t) => App(do_rename(f, from, to), do_rename(t, from, to))
    case AppStep1(f, t) => AppStep1(do_rename(f, from, to), do_rename(t, from, to))
    case AppStep2(f, t) => AppStep2(do_rename(f, from, to), do_rename(t, from, to))
    case op:Op => Op(op.op, list_rename(op.l, from, to))
    case _ => t
  }
}

//find bv in t and change the bv that makes bv not equals to fv

def rename(t: term, restriction: term) : term = {
  @tailrec
  def rename_helper(bv: Set[String], fv: Set[String], l: List[String], t: term): term = l match {
    case a :: b => rename_helper(bv, fv, b, do_rename(t, a, find_to(bv, fv, a)))
    case _ => t
  }

  val bv = BV(t)
  val fv = FV(restriction)
  rename_helper(bv, fv, bv.intersect(fv).toList, t)
}

//substitute the terms in t1 from "from" to "to"

def substitute(t1: term, from: term, to: term): term = {
  //tail rec later
  def list_substitue(l: List[term], from: term, to: term): List[term] = l match {
    case h :: t =>
      substitute(h, from, to) :: list_substitue(t, from, to)
    case _ => Nil
  }

  t1 match {
    case Var(_) if t1 == from => to
    case Fun(x1, t3) if Var(x1) != from => Fun(x1, substitute(t3, from, to))
    case FunStep1(x1, t3) if Var(x1) != from =>
      val ft = substitute(t3, from, to)
      if (ft == t3) FunStep1(x1, t3)
      else Fun(x1, ft)
    case App(f, t3) => App(substitute(f, from, to), substitute(t3, from, to))
    case AppStep1(f, t3) =>
      val fs = substitute(f, from, to)
      val ts = substitute(t3, from, to)
      if (ts != t3) App(fs, ts)
      else AppStep1(fs, ts)
    case AppStep2(f, t3) =>
      val fs = substitute(f, from, to)
      val ts = substitute(t3, from, to)
      if (ts != t3) App(fs, ts)
      else if (fs != f) AppStep1(fs, ts)
      else AppStep2(fs, ts)
    case Op(op, l) => Op(op, list_substitue(l, from, to))
    case _ => t1
  }
}

def try_op(op:Op): term = {//revise it!
  val param = op.l
  op.op match {
    case "if" => If(param.head, param.tail.head, param.tail.tail.head)
    case "eq" => Eq(param.head, param.tail.head)
  }
}

def small_step(t:term):term = t match {
  case Fun(x, t) =>
    val tmp = small_step(t)
    if (tmp == t) FunStep1(x, t)
    else Fun(x, tmp)
  case App(f, t) => t match {
    case Var(_) => AppStep1(f, t)
    case True => AppStep1(f, t)
    case False => AppStep1(f, t)
    case Num(_) => AppStep1(f, t)
    case op: Op =>
      val tmp = small_step(op)
      if (op == tmp) AppStep1(f, t)
      else App(f, tmp)
    case FunStep1(_, _) => AppStep1(f, t)
    case AppStep2(_, _) => AppStep1(f, t)
    case _ => App(f, small_step(t))
  }
  case AppStep1(f, t) => f match {
    case Var(_) => AppStep2(f, t)
    case True => Wrong
    case False => Wrong
    case Num(_) => Wrong
    case op: Op =>
      val tmp = small_step(op)
      if (op == tmp) AppStep2(f, t)
      else AppStep1(tmp, t)
    case FunStep1(_, _) =>
      rename(f, t) match {
        case FunStep1(x, ft) => substitute(ft, Var(x), t)
      }
    case AppStep2(_, _) => AppStep2(f, t)
    case _ => AppStep1(small_step(f), t)
  }
  case op: Op => try_op(op)
  case _ => t
}

//convert abstract to concrete

def concrete(t:term):String = {
  def list_concrete(l: List[term]): String = {
    @tailrec
    def list_concrete_helper(l: List[term], res: String): String = l match {
      case h :: t => list_concrete_helper(t, res + " " + concrete(h))
      case _ => res
    }

    list_concrete_helper(l, "")
  }

  t match {
    case Var(x) => x
    case Fun(x, t) => "{^"+x+"."+concrete(t) + "}"
    case FunStep1(x, t) => concrete(Fun(x, t))
    case App(f, t) => t match {
      case App(_, _) => concrete(f) + " ( " + concrete(t) + " )"
      case AppStep1(_, _) => concrete(f) + " ( " + concrete(t) + " )"
      case AppStep2(_, _) => concrete(f) + " ( " + concrete(t) + " )"
      case _ => concrete(f) + " " + concrete(t)
    }
    case AppStep1(f, t) => concrete(App(f, t))
    case AppStep2(f, t) => concrete(App(f, t))
    case True => "true"
    case False => "false"
    case Num(n) => "" + n
    case Op(op, l) => " ( " + op + ":" + list_concrete(l) + " ) "
  }
}

def big_step(t:term):String = {
  var prev = t
  var res = t
  //    var cnt = 0
  do {
    //        println(cnt + ": " + concrete(res))
    //        cnt = cnt + 1
    do {
      prev = res
      res = small_step(prev)
    } while (concrete(res) == concrete(prev) && res != prev)
  } while(res != prev)
  concrete(res)
}

//test cases

//big_step(Id())
////Id
//big_step(App(Id(), Id()))
////Id
//
//big_step(App(App(LCTrue(), Id()), Id()))
////Id
//big_step(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
////True
//big_step(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
////True
//
//big_step(App(App(And(), LCTrue()), LCTrue()))
////True
//big_step(App(App(And(), LCTrue()), LCFalse()))
////False
//big_step(App(App(And(), LCFalse()), LCTrue()))
////False
//big_step(App(App(And(), LCFalse()), LCFalse()))
////False
//big_step(App(App(Or(), LCTrue()), LCTrue()))
////True
//big_step(App(App(Or(), LCTrue()), LCFalse()))
////True
//big_step(App(App(Or(), LCFalse()), LCTrue()))
////True
//big_step(App(App(Or(), LCFalse()), LCFalse()))
////False
//big_step(App(Not(), LCTrue()))
////False
//big_step(App(Not(), LCFalse()))
////True
//
//big_step(App(First(), App(App(Pair(), LCTrue()), LCFalse())))
////True
//big_step(App(Second(), App(App(Pair(), LCTrue()), LCFalse())))
////False
//
//big_step(Church(0))
////Zero
//big_step(App(Succ(),Church(0)))
////One
//big_step(App(Succ(), App(Succ(),Church(0))))
////Two
//big_step(App(Succ(), App(Succ(), App(Succ(),Church(0)))))
////Three
//big_step(App(App(Plus(), Church(0)), Church(0)))
////Zero
//big_step(App(App(Plus(), Church(0)), Church(1)))
////One
//big_step(App(App(Plus(), Church(3)), Church(4)))
////Seven
//big_step(App(App(Mult(), Church(1)), Church(2)))
////Two
//big_step(App(App(Mult(), Church(2)), Church(4)))
////Eight
//big_step(App(App(Power(), Church(2)), Church(2)))
////Four
//big_step(App(App(Power(), Church(3)), Church(2)))
////Nine
//
//big_step(App(IsZero(), Church(0)))
////True
//big_step(App(IsZero(), Church(4)))
////False
//big_step(App(Pred(), Church(0)))
////Zero
//big_step(App(Pred(), Church(4)))
////Four
//big_step(App(App(Sub(), Church(7)), Church(2)))
////Five
//big_step(App(App(Sub(), Church(3)), Church(5)))
////Zero
//big_step(App(App(Equal(), Church(0)), Church(0)))
////True
//big_step(App(App(Equal(), Church(5)), Church(5)))
////True
//big_step(App(App(Equal(), Church(3)), Church(8)))
////False
//big_step(App(App(Equal(), Church(10)), Church(6)))
////False

//val list1 = App(App(Cons(), Church(3)), App(App(Cons(), Church(2)), EmptyList()))
//big_step(list1)
//big_step(App(Head(), list1))
////Three
//big_step(App(IsNil(), EmptyList()))
////True
//big_step(App(IsNil(), list1))
////False
//big_step(App(PopFront(), list1))
////{^c.{^n.c Two n}}
//big_step(App(Tail(), list1))
////{^c.{^n.c Two n}}
//val list2 = App(App(Cons(), EmptyList()), App(App(Cons(), Church(4)), list1))
//big_step(list2)
//big_step(App(PopFront(), list2))
////{^c.{^n.c Four (c Three (c Two n))}}
//big_step(App(Tail(), list2))
////{^c.{^n.c Two n}}

big_step(If(True, False, LCFalse()))
//False
big_step(If(False, False, LCFalse()))
//false
big_step(App(Fun("x", If(Var("x"), False, LCFalse())), True))
//False
big_step(App(Fun("x", If(Var("x"), False, LCFalse())), False))
//false
big_step(Eq(Num(1), Num(3)))
//false
big_step(Eq(Num(3), Num(3)))
//true
big_step(App(Fun("x", Eq(Var("x"), Num(3))), Num(1)))
//false
big_step(App(Fun("x", Eq(Var("x"), Num(5))), Num(5)))
//true