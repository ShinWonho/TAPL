//full beta-reduction + shadowing + concrete

import scala.annotation.tailrec

trait term

case class Var(x: String) extends term

case class Fun(x: String, t: term) extends term

case class FunStep1(x:String, t:term) extends term

case class App(f: term, t: term) extends term

case class AppStep1(f: term, t: term) extends term

case class AppStep2(f: term, t: term) extends term

case object Wrong extends term

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
def Plus() = Fun("m", Fun("n", Fun("s", Fun("z", App(App(Var("m"), Var("s")), App(App(Var("n"), Var("s")), Var("z")))))))
def Mult() = Fun("m", Fun("n", App(App(Var("m"), App(Plus(), Var("n"))), Church(0))))

def substitute(t1: term, x: String, t2: term): term = t1 match {
  case Var(x1) if x1 == x => t2
  case Fun(x1, t3) =>
    if (x1 != x) Fun(x1, substitute(t3, x, t2))
    else t1
  case FunStep1(x1, t3) =>
    if (x1 != x) {
      val ft = substitute(t3, x, t2)
      if (ft == t3) FunStep1(x1, t3)
      else Fun(x1, ft)
    }
    else t1
  case App(f, t3) => App(substitute(f, x, t2), substitute(t3, x, t2))
  case AppStep1(f, t3) =>
    val fs = substitute(f, x, t2)
    val ts = substitute(t3, x, t2)
    if (ts != t3) App(fs, ts)
    else AppStep1(fs, ts)
  case AppStep2(f, t3) =>
    val fs = substitute(f, x, t2)
    val ts = substitute(t3, x, t2)
    if (ts != t3) App(fs, ts)
    else if (fs != f) AppStep1(fs, ts)
    else AppStep2(fs, ts)
  case _ => t1
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
    case Wrong => f
    case _ => App(f, small_step(t))
  }
  case AppStep1(f, t) => f match {
    case Var(_) => AppStep2(f, t)
    case FunStep1(x, ft) => substitute(ft, x, t)
    case AppStep2(_, _) => AppStep2(f, t)
    case Wrong => f
    case _ => AppStep1(small_step(f), t)
  }
  case _ => t
}

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
  case Wrong => "Wrong"
}

def big_step(t:term):String = {
  var prev = t
  var res = t
  var cnt = 0
  do {
    println(cnt + ": " + concrete(res))
    cnt = cnt + 1
    prev = res
    res = small_step(prev)
  } while(res != prev)
  concrete(res)
}

//test cases

concrete(App(Id(), App(Id(), Id())))

big_step(Id())
//LCId
big_step(App(Id(), Id()))
//LCId

big_step(App(App(True(), Id()), Id()))
//LCId
big_step(App(App(Fun("x", Fun("y", Var("x"))), True()), False()))
//LCTrue
big_step(App(App(App(If(), True()), True()), False()))
//LCTrue

big_step(App(App(And(), True()), True()))
//LCTrue
big_step(App(App(And(), True()), False()))
//LCFalse
big_step(App(App(And(), False()), True()))
//LCFalse
big_step(App(App(And(), False()), False()))
//LCFalse
big_step(App(App(Or(), True()), True()))
//LCTrue
big_step(App(App(Or(), True()), False()))
//LCTrue
big_step(App(App(Or(), False()), True()))
//LCTrue
big_step(App(App(Or(), False()), False()))
//LCFalse
big_step(App(Not(), True()))
//LCFalse
big_step(App(Not(), False()))
//LCTrue

big_step(App(First(), App(App(Pair(), True()), False())))
//LCTrue
big_step(App(Second(), App(App(Pair(), True()), False())))
//LCFalse

big_step(Church(0))
//LCZero
big_step(Church(1))
//LCOne
big_step(Church(2))
//LCTwo
big_step(Church(3))
//LCThree
big_step(Church(4))
//LCFour
big_step(App(App(Plus(), Church(0)), Church(0)))
//LCZero
big_step(App(App(Plus(), Church(0)), Church(1)))
//LCOne
big_step(App(App(Plus(), Church(3)), Church(4)))
//LCSeven
big_step(App(App(Mult(), Church(1)), Church(2))) // shadowing problem!
