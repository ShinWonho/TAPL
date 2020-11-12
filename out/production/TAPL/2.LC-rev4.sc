//language features

trait term
case class Var(x:String) extends term
case class Fun(x:String, t:term) extends term
case class App(f:term, t:term) extends term
case object Wrong extends term

//functions

def EmptyMap(): Map[String, term] = Map[String, term]()

//features

class FunClass() {
  def LCId(x: String): term = Fun(x, Var(x))

  def LCId(): term = LCId("x_")

  //boolean

  def LCTrue(t: String, f: String): term = Fun(t, Fun(f, Var(t)))

  def LCTrue(): term = LCTrue("tx1_", "tx2_")

  def LCFalse(t: String, f: String): term = Fun(t, Fun(f, Var(f)))

  def LCFalse(): term = LCFalse("fx1_", "fx2_")

  def LCIf(c: String, t: String, f: String): term = Fun(c, Fun(t, Fun(f, App(App(Var(c), Var(t)), Var(f)))))

  def LCIf(): term = LCIf("c_", "t_", "f_")

  //boolean operation

  def LCAnd(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), Var(b)), LCFalse("and_t", "and_f"))))

  def LCAnd(): term = LCAnd("a_", "b_")

  def LCOr(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), LCTrue("or_t", "or_f")), Var(b))))

  def LCOr(): term = LCOr("a_", "b_")

  def LCNot(a: String): term = Fun(a, App(App(App(LCIf("c_", "t_", "f_"), Var(a)), LCFalse("false_t", "false_f")), LCTrue("true_t", "true_f")))

  def LCNot(): term = LCNot("a_")

  //pair

  def LCPair(a: String, b: String, s: String): term = Fun(a, Fun(b, Fun(s, App(App(Var(s), Var(b)), Var(a)))))

  def LCPair(): term = LCPair("a_", "b_", "s_")

  def LCFirst(p: String): term = Fun(p, App(Var(p), LCFalse("t_", "f_")))

  def LCFirst(): term = LCFirst("p_")

  def LCSecond(p: String): term = Fun(p, App(Var(p), LCTrue("t_", "f_")))

  def LCSecond(): term = LCSecond("p_")

  //church numeral

  def LCZero():term = LCFalse("s_", "z_")

  def LCSucc(n:String, s:String, z:String):term = Fun(n, Fun(s, Fun(z, App(Var(s), App(App(Var(n), Var(s)), Var(z))))))

  def LCSucc():term = LCSucc("n_", "s_", "z_")
}

//evaluation

def substitute(t1:term, x:String, t2:term):term = t1 match {
  case Var(x1) if x1 == x => t2
  case App(f, t3) => App(substitute(f, x, t2), substitute(t3, x, t2))
  case Fun(x1, t3) => Fun(x1, substitute(t3, x, t2))
  case _ => t1
}

def eval(t:term):term = t match {
  case Var(x) =>
    println("free_variable: " + x)
    Wrong
  case App(f, t1) => eval(f) match {
    case Fun(x, t2) => eval(substitute(t2, x, eval(t1)))
    case _ =>
      println("Not a function : " + f)
      Wrong
  }
  case _ => t
}

//test cases

val f = new FunClass()

eval(f.LCId())
//LCId
eval(App(f.LCId(), f.LCId()))
//LCId

eval(App(App(f.LCTrue(), f.LCId()), f.LCId("y")))
//LCId
eval(App(App(Fun("x", Fun("y", Var("x"))), f.LCTrue()), f.LCFalse()))
//LCTrue
eval(App(App(App(f.LCIf(), f.LCTrue()), f.LCTrue()), f.LCFalse()))
//LCTrue

eval(App(App(f.LCAnd(), f.LCTrue()), f.LCTrue()))
//LCTrue
eval(App(App(f.LCAnd(), f.LCTrue()), f.LCFalse()))
//LCFalse
eval(App(App(f.LCAnd(), f.LCFalse()), f.LCTrue()))
//LCFalse
eval(App(App(f.LCAnd(), f.LCFalse()), f.LCFalse()))
//LCFalse
eval(App(App(f.LCOr(), f.LCTrue()), f.LCTrue()))
//LCTrue
eval(App(App(f.LCOr(), f.LCTrue()), f.LCFalse()))
//LCTrue
eval(App(App(f.LCOr(), f.LCFalse()), f.LCTrue()))
//LCTrue
eval(App(App(f.LCOr(), f.LCFalse()), f.LCFalse()))
//LCFalse
eval(App(f.LCNot(), f.LCTrue()))
//LCFalse
eval(App(f.LCNot(), f.LCFalse()))
//LCTrue

eval(App(f.LCFirst(), App(App(f.LCPair(), f.LCTrue()), f.LCFalse())))
//LCTrue
eval(App(f.LCSecond(), App(App(f.LCPair(), f.LCTrue()), f.LCFalse())))
//LCFalse

eval(f.LCZero())
//LCZero
eval(App(f.LCSucc(), f.LCZero()))
//LCOne