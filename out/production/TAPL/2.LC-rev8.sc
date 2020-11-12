//full beta-reduction

import scala.annotation.tailrec

trait term

case class Var(x: String) extends term

case class Fun(x: String, t: term) extends term

case class FunStep1(x:String, t:term) extends term

case class App(f: term, t: term) extends term

case class AppStep1(f: term, t: term) extends term

case class AppStep2(f: term, t: term) extends term

case object Wrong extends term

class LC {

  def EmptyMap(): Map[String, term] = Map[String, term]()

  //features
  def Id(x: String): term = Fun(x, Var(x))

  //boolean
  def True(t: String, f: String): term = Fun(t, Fun(f, Var(t)))
  def False(t: String, f: String): term = Fun(t, Fun(f, Var(f)))
  def If(c: String, t: String, f: String): term = Fun(c, Fun(t, Fun(f, App(App(Var(c), Var(t)), Var(f)))))

  //boolean operation
  def And(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), Var(b)), False("af1", "af2_"))))
  def Or(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), True("ot1", "ot2")), Var(b))))
  def Not(a: String): term = Fun(a, App(App(App(If("nc", "nt", "nf"), Var(a)), False("nf1", "nf2")), True("nt1", "nt2")))

  //pair
  def Pair(a: String, b: String, s: String): term = Fun(a, Fun(b, Fun(s, App(App(Var(s), Var(b)), Var(a)))))
  def First(p: String): term = Fun(p, App(Var(p), False("1f1", "1f2")))
  def Second(p: String): term = Fun(p, App(Var(p), True("2t1", "2t2")))

  //church numeral

  def Succ(n: String, s: String, z: String): term = Fun(n, Fun(s, Fun(z, App(Var(s), App(App(Var(n), Var(s)), Var(z))))))
  def Plus(m: String, n: String, s: String, z: String) = Fun(m, Fun(n, Fun(s, Fun(z, App(App(Var(m), Var(s)), App(App(Var(n), Var(s)), Var(z)))))))
}

def refresh(t:term):term = t match {
  case FunStep1(x, t) => Fun(x, refresh(t))
  case AppStep1(f, t) => App(refresh(f), refresh(t))
  case AppStep2(f, t) => App(refresh(f), refresh(t))
  case _ => t
}

def substitute(t1: term, x: String, t2: term): term = t1 match {
  case Var(x1) if x1 == x => t2
  case Fun(x1, t3) => Fun(x1, substitute(t3, x, t2))
  case FunStep1(x1, t3) =>
    val ft = substitute(t3, x, t2)
    if (ft == t3) FunStep1(x1, t3)
    else Fun(x1, ft)
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

def big_step(t:term):term = {
  var prev = t
  var res = t
//  var cnt = 0
  do {
//    println(cnt + ": " + res)
//    cnt = cnt + 1
    prev = res
    res = small_step(prev)
  } while(res != prev)
  refresh(res)
}

//test cases

val LC = new LC()

def Id(n:Int): term = LC.Id(""+n)

//boolean
def True(n:Int): term = LC.True("t"+(2*n), "t"+(2*n+1))
def False(n:Int): term = LC.False("f"+(2*n), "f"+(2*n+1))
def If(n:Int): term = LC.If("ifc"+n, "ift"+n, "iff"+n)

//boolean operation
def And(n:Int): term = LC.And("&a"+n, "&b"+n)
def Or(n:Int): term = LC.Or("|a"+n, "|b"+n)
def Not(n:Int): term = LC.Not("~a"+n)

//pair
def Pair(n:Int): term = LC.Pair("a"+n, "b"+n, "select"+n)
def First(n:Int): term = LC.First("p1"+n)
def Second(n:Int): term = LC.Second("p2"+n)

//church numeral
@tailrec
def Church_helper(n:Int, index:Int, t:term):term = n match {
  case 0 => t
  case _ => Church_helper(n - 1, index, App(Var("s"+index), t))
}
def Church(n:Int, index:Int):term = Church_helper(n, index, LC.False("s"+index, "z"+index))
def Succ(n:Int): term = LC.Succ("n"+n, "s"+n, "z"+n)
def Zero(n:Int):term = Church(0, n)
def One(n:Int):term = Church(1, n)
def Two(n:Int):term = Church(2, n)
def Three(n:Int):term = Church(3, n)
def Four(n:Int):term = Church(4, n)
def Plus(n:Int) = LC.Plus("pm"+n, "pn"+n, "ps"+n, "pz"+n)

big_step(Id(1))
//LCId
big_step(App(Id(1), Id(2)))
//LCId

big_step(App(App(True(1), Id(1)), Id(2)))
//LCId
big_step(App(App(Fun("x", Fun("y", Var("x"))), True(1)), False(2)))
//LCTrue
big_step(App(App(App(If(1), True(1)), True(2)), False(1)))
//LCTrue

big_step(App(App(And(1), True(1)), True(2)))
//LCTrue
big_step(App(App(And(1), True(1)), False(1)))
//LCFalse
big_step(App(App(And(1), False(1)), True(1)))
//LCFalse
big_step(App(App(And(1), False(1)), False(2)))
//LCFalse
big_step(App(App(Or(1), True(1)), True(2)))
//LCTrue
big_step(App(App(Or(1), True(1)), False(1)))
//LCTrue
big_step(App(App(Or(1), False(1)), True(1)))
//LCTrue
big_step(App(App(Or(1), False(1)), False(2)))
//LCFalse
big_step(App(Not(1), True(1)))
//LCFalse
big_step(App(Not(1), False(1)))
//LCTrue

big_step(App(First(1), App(App(Pair(1), True(1)), False(1))))
//LCTrue
big_step(App(Second(1), App(App(Pair(1), True(1)), False(1))))
//LCFalse

big_step(Zero(0))
//LCZero
big_step(One(0))
//LCOne()
big_step(Two(0))
//LCTwo()
big_step(Three(0))
//LCThree()
big_step(Four(0))
//LCFour()
big_step(App(App(Plus(0), Three(0)), Four(0)))//chuch numeral func has error
//LCSeven()
big_step(App(Fun("x", Fun("x", Var("x"))), True(0)))
