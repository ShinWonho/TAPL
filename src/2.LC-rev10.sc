//full beta-reduction + shadowing_change_if_needed + concrete

import scala.annotation.tailrec

trait term

case class Var(x: String) extends term

case class Fun(x: String, t: term) extends term

case class FunStep1(x:String, t:term) extends term

case class App(f: term, t: term) extends term

case class AppStep1(f: term, t: term) extends term

case class AppStep2(f: term, t: term) extends term

//default
def Id(): term = Fun("x", Var("x"))

//boolean
def True(): term = Fun("t", Fun("f", Var("t")))
def False(): term = Fun("t", Fun("f", Var("f")))
def If(): term = Fun("c", Fun("t", Fun("f", App(App(Var("c"), Var("t")), Var("f")))))

//boolean operation
def And(): term = Fun("a", Fun("b", App(App(Var("a"), Var("b")), False())))
def Or(): term = Fun("a", Fun("b", App(App(Var("a"), True()), Var("b"))))
def Not(): term = Fun("a", App(App(App(If(), Var("a")), False()), True()))

//pair
def Pair(): term = Fun("a", Fun("b", Fun("s", App(App(Var("s"), Var("b")), Var("a")))))
def First(): term = Fun("p", App(Var("p"), False()))
def Second(): term = Fun("p", App(Var("p"), True()))

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
def IsZero(): term = Fun("m", App(App(Var("m"),Fun("x", False())), True()))
def ZeroPair(): term = App(App(Pair(), Church(0)), Church(0))
def SuccPair(): term = Fun("p", App(App(Pair(), App(Second(), Var("p"))), App(Succ(), App(Second(), Var("p")))))
def Pred(): term = Fun("m", App(First(), App(App(Var("m"), SuccPair()), ZeroPair())))
def Sub(): term = Fun("m", Fun("n", App(App(Var("n"), Pred()), Var("m"))))
def Equal(): term = Fun("m", Fun("n", App(App(And(), App(IsZero(), App(App(Sub(), Var("m")), Var("n")))), App(IsZero(), App(App(Sub(), Var("n")), Var("m"))))))

def EmptyList(): term = Fun("c", Fun("n", Var("n")))
def Cons(): term = Fun("e", Fun("l", Fun("c", Fun("n", App(App(Var("c"), Var("e")), App(App(Var("l"), Var("c")), Var("n")))))))
def Head(): term = Fun("l", App(App(Var("l"), True()), EmptyList()))
def AlwaysFalse(): term = Fun("c", Fun("n", False()))
def IsNil(): term = Fun("l", App(App(Var("l"), AlwaysFalse()), True()))
def EmptyPair(): term = App(App(Pair(), EmptyList()), EmptyList())
def ConsPair(): term = Fun("e", Fun("p", App(App(Pair(), App(Second(), Var("p"))), App(App(Cons(), Var("e")), App(Second(), Var("p"))))))
def PopFront(): term = Fun("l", App(First(), App(App(Var("l"), ConsPair()), EmptyPair())))
def ConsTail(): term = Fun("e", Fun("l", App(App(App(If(), App(IsNil(), Var("l"))), App(App(Cons(), Var("e")), EmptyList())), Var("l"))))
def Tail(): term = Fun("l", App(App(App(App(Var("l"), ConsTail()), EmptyList()), True()), EmptyList()))


//find free variables

def FV_helper(s:Set[String], t:term):Set[String] = t match {
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
}

def FV(t: term): Set[String] = FV_helper(Set[String](), t)

//find binding variable

def BV_helper(s: Set[String], t: term): Set[String] = t match {
  case Var(_) => s
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
}

def BV(t: term): Set[String] = BV_helper(Set[String](), t)

//make replacing string

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

def mk_to(from: String): String = {
  mk_to_helper(from.toList, 0).mkString("")
}

@tailrec
def find_to(bv: Set[String], fv: Set[String], from: String): String = {
  if ((bv++fv).contains(from)) find_to(bv, fv, mk_to(from))
  else from
}

//rename from "from" to "to"

def do_rename(t: term, from: String, to: String): term = t match {
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
  case _ => t
}

@tailrec
def rec_helper(bv: Set[String], fv: Set[String], l: List[String], t: term): term = l match {
  case a :: b => rec_helper(bv, fv, b, do_rename(t, a, find_to(bv, fv, a)))
  case _ => t
}

//find bv in t and change the bv that makes bv not equals to fv

def rename(t: term, restriction: term) : term = {
  val bv = BV(t)
  val fv = FV(restriction)
  rec_helper(bv, fv, bv.intersect(fv).toList, t)
}

//substitute the terms in t1 from "from" to "to"

def substitute(t1: term, from: term, to: term): term = {
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
    case _ => t1
  }
}

def small_step(t:term):term = t match {
  case Fun(x, t) =>
    val tmp = small_step(t)
    if (tmp == t) FunStep1(x, t)
    else Fun(x, tmp)
  case App(f, t) => t match {
    case Var(_) => AppStep1(f, t)
    case FunStep1(_, _) => AppStep1(f, t)
    case AppStep2(_, _) => AppStep1(f, t)
    case _ => App(f, small_step(t))
  }
  case AppStep1(f, t) => f match {
    case Var(_) => AppStep2(f, t)
    case FunStep1(_, _) =>
      rename(f, t) match {
        case FunStep1(x, ft) => substitute(ft, Var(x), t)
//        case _ =>
//          println("unreachable case")
//          Var("Wrong")
      }
    case AppStep2(_, _) => AppStep2(f, t)
    case _ => AppStep1(small_step(f), t)
  }
  case _ => t
}

//convert abstract to concrete

def concrete(t:term):String = t match {
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
//big_step(App(App(True(), Id()), Id()))
////Id
//big_step(App(App(Fun("x", Fun("y", Var("x"))), True()), False()))
////True
//big_step(App(App(App(If(), True()), True()), False()))
////True
//
//big_step(App(App(And(), True()), True()))
////True
//big_step(App(App(And(), True()), False()))
////False
//big_step(App(App(And(), False()), True()))
////False
//big_step(App(App(And(), False()), False()))
////False
//big_step(App(App(Or(), True()), True()))
////True
//big_step(App(App(Or(), True()), False()))
////True
//big_step(App(App(Or(), False()), True()))
////True
//big_step(App(App(Or(), False()), False()))
////False
//big_step(App(Not(), True()))
////False
//big_step(App(Not(), False()))
////True
//
//big_step(App(First(), App(App(Pair(), True()), False())))
////True
//big_step(App(Second(), App(App(Pair(), True()), False())))
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

val list1 = App(App(Cons(), Church(3)), App(App(Cons(), Church(2)), EmptyList()))
big_step(list1)
big_step(App(Head(), list1))
//Three
big_step(App(IsNil(), EmptyList()))
//True
big_step(App(IsNil(), list1))
//False
big_step(App(PopFront(), list1))
//{^c.{^n.c Two n}}
big_step(App(Tail(), list1))
//{^c.{^n.c Two n}}
val list2 = App(App(Cons(), EmptyList()), App(App(Cons(), Church(4)), list1))
big_step(list2)
big_step(App(PopFront(), list2))
//{^c.{^n.c Four (c Three (c Two n))}}
big_step(App(Tail(), list2))
//{^c.{^n.c Two n}}