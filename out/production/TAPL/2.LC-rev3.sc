//language features

trait term
case class Var(x:String) extends term
case class Fun(x:String, t:term) extends term
case class SimFun(x:String, t:term) extends term
case class App(f:term, t:term) extends term
case object Wrong extends term

trait Value
case class CloV(env:Map[String, Value], x:String, t:term) extends Value
case object ErrorV extends Value

//functions

def EmptyMap(): Map[String, Value] = Map[String, Value]()

//features

class FunClass() {
  def LCId(x: String): term = Fun(x, Var(x))

  def LCId(): term = LCId("x_")

  def LCTrue(t: String, f: String): term = Fun(t, Fun(f, Var(t)))

  def LCTrue(): term = LCTrue("tx1_", "tx2_")

  def LCFalse(t: String, f: String): term = Fun(t, Fun(f, Var(f)))

  def LCFalse(): term = LCFalse("fx1_", "fx2_")

  def LCIf(c: String, t: String, f: String): term = Fun(c, Fun(t, Fun(f, App(App(Var(c), Var(t)), Var(f)))))

  def LCIf(): term = LCIf("c_", "t_", "f_")

  def LCAnd(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), Var(b)), LCFalse("and_t", "and_f"))))

  def LCAnd(): term = LCAnd("a_", "b_")

  def LCOr(a: String, b: String): term = Fun(a, Fun(b, App(App(Var(a), LCTrue("and_t", "and_f")), Var(b))))

  def LCOr(): term = LCOr("a_", "b_")

  def LCNot(a: String): term = Fun(a, App(App(App(LCIf("c_", "t_", "f_"), Var(a)), LCFalse("false_t", "false_f")), LCTrue("true_t", "true_f")))

  def LCNot(): term = LCNot("a_")

  def LCPair(a: String, b: String, s: String): term = Fun(a, Fun(b, Fun(s, App(App(Var(s), Var(b)), Var(a)))))

  def LCPair(): term = LCPair("a_", "b_", "s_")

  def LCFirst(p: String): term = Fun(p, App(Var(p), LCFalse("t_", "f_")))

  def LCFirst(): term = LCFirst("p_")

  def LCSecond(p: String): term = Fun(p, App(Var(p), LCTrue("t_", "f_")))

  def LCSecond(): term = LCSecond("p_")
}

//evaluation

def eval_helper(t:term, env:Map[String,Value]):Value = {
  val res = t match {
    case Var(x) => env(x)
    case App(f, t1) => eval_helper(f, env) match {
      case CloV(m2, x2, t2) => eval_helper(t2, m2 + (x2 -> eval_helper(t1, env)))
      case _ =>
        println("Not a function : " + f)
        ErrorV
    }
    case Fun(x, t) => CloV(env, x, t)
    case Wrong => ErrorV
  }
  println(res)
  res
}

def eval(t:term):Value = {
  val m = EmptyMap()
  eval_helper(t, m)
}

//test cases

val f = new FunClass()

eval(f.LCId())
//Clov(Map(), "x", Var("x"))
eval(App(f.LCId(), f.LCId()))
//Clov(Map(), "x", Var("x"))

eval(App(App(f.LCTrue(), f.LCId()), f.LCId()))
//IDx
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