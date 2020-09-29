//full beta-reduction

trait term

case class Var(x: String) extends term

case class Fun(x: String, t: term) extends term

case class App(f: term, t: term) extends term

case object Wrong extends term

class LC {

  //functions

  def EmptyMap(): Map[String, term] = Map[String, term]()

  //features

  def LCId(x: String): term = Fun(x, Var(x))

  //boolean

  def LCTrue(t: String, f: String): term = Fun(t, Fun(f, Var(t)))

  def LCFalse(t: String, f: String): term = Fun(t, Fun(f, Var(f)))

  def LCIf(c: String, t: String, f: String): term = Fun(c, Fun(t, Fun(f, App(App(Var(c), Var(t)), Var(f)))))

  //boolean operation

  def LCAnd(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), Var(b)), LCFalse("and_t", "and_f"))))

  def LCOr(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), LCTrue("or_t", "or_f")), Var(b))))

  def LCNot(a: String): term = Fun(a, App(App(App(LCIf("c_", "t_", "f_"), Var(a)), LCFalse("false_t", "false_f")), LCTrue("true_t", "true_f")))

  //pair

  def LCPair(a: String, b: String, s: String): term = Fun(a, Fun(b, Fun(s, App(App(Var(s), Var(b)), Var(a)))))

  def LCFirst(p: String): term = Fun(p, App(Var(p), LCFalse("t_", "f_")))

  def LCSecond(p: String): term = Fun(p, App(Var(p), LCTrue("t_", "f_")))

  //church numeral

  def LCSucc(n: String, s: String, z: String): term = Fun(n, Fun(s, Fun(z, App(Var(s), App(App(Var(n), Var(s)), Var(z))))))

  def LCPlus(m: String, n: String, s: String, z:String) = Fun(m, Fun(n, Fun(s, Fun(z, App(App(Var(m), Var(s)), App(App(Var(n), Var(s)), Var(z)))))))

  //evaluation

  def substitute(t1: term, x: String, t2: term): term = t1 match {
    case Var(x1) if x1 == x => t2
    case App(f, t3) => eval(App(substitute(f, x, t2), substitute(t3, x, t2)))
    case Fun(x1, t3) => Fun(x1, substitute(t3, x, t2))
    case _ => t1
  }

  def eval(t: term): term = t match {
    case App(f, t1) => eval(f) match {
      case Fun(x, t2) => eval(substitute(t2, x, eval(t1)))
      case _ => t
    }
    case _ => t
  }
}

//test helper function

val lc = new LC()

def LCId(): term = lc.LCId("x_")

//boolean

def LCTrue(): term = lc.LCTrue("tx1_", "tx2_")

def LCFalse(): term = lc.LCFalse("fx1_", "fx2_")

def LCIf(): term = lc.LCIf("c_", "t_", "f_")

//boolean operation

def LCAnd(): term = lc.LCAnd("a_", "b_")

def LCOr(): term = lc.LCOr("a_", "b_")

def LCNot(): term = lc.LCNot("a_")

//pair

def LCPair(): term = lc.LCPair("a_", "b_", "s_")

def LCFirst(): term = lc.LCFirst("p_")

def LCSecond(): term = lc.LCSecond("p_")

//church numeral

def LCZero():term = LCFalse()

def LCSucc():term = lc.LCSucc("n_", "s_", "z_")

def LCPlus():term = lc.LCPlus("m_", "n_", "s_", "z_")

def eval(t:term):term = lc.eval(t)

//test cases

eval(LCId())
//LCId
eval(App(LCId(), LCId()))
//LCId

eval(App(App(LCTrue(), LCId()), lc.LCId("y")))
//LCId
eval(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
//LCTrue
eval(App(App(App(LCIf(), lc.LCTrue("t", "f")), LCTrue()), LCFalse()))
//LCTrue

eval(App(App(LCAnd(), LCTrue()), LCTrue()))
//LCTrue
eval(App(App(LCAnd(), LCTrue()), LCFalse()))
//LCFalse
eval(App(App(LCAnd(), LCFalse()), LCTrue()))
//LCFalse
eval(App(App(LCAnd(), LCFalse()), LCFalse()))
//LCFalse
eval(App(App(LCOr(), LCTrue()), LCTrue()))
//LCTrue
eval(App(App(LCOr(), LCTrue()), LCFalse()))
//LCTrue
eval(App(App(LCOr(), LCFalse()), LCTrue()))
//LCTrue
eval(App(App(LCOr(), LCFalse()), LCFalse()))
//LCFalse
eval(App(LCNot(), LCTrue()))
//LCFalse
eval(App(LCNot(), LCFalse()))
//LCTrue

eval(App(LCFirst(), App(App(LCPair(), LCTrue()), LCFalse())))
//LCTrue
eval(App(LCSecond(), App(App(LCPair(), LCTrue()), LCFalse())))
//LCFalse

eval(LCZero())
//LCZero
def LCOne():term = eval(App(LCSucc(), LCZero()))
LCOne()

def LCTwo():term = eval(App(LCSucc(), App(LCSucc(), LCZero())))
LCTwo()

def LCThree(): term = eval(App(LCSucc(), App(LCSucc(), App(LCSucc(), LCZero()))))
LCThree()

def LCFour():term = eval(App(App(LCPlus(), LCOne()), LCThree()))
LCFour()

eval(App(App(App(App(LCPlus(), LCTwo()), LCZero()), LCThree()), LCZero()))