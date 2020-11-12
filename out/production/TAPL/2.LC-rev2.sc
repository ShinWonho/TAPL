//language features

trait term
case class Var(x:String) extends term
case class Fun(env:Map[String, term], x:String, t:term) extends term
case class SimFun(x:String, t:term) extends term
case class App(f:term, t:term) extends term
case object Wrong extends term

//functions

def EmptyMap(): Map[String, term] = Map[String, term]()

def mkFun(x:String, t:term):term = Fun(EmptyMap(), x, t)

def revFun_helper(t:term):term = t match {
  case Fun(_, x, t) => SimFun(x, revFun_helper(t))
  case App(f, t) =>
    val sf = revFun_helper(f)
    val st = revFun_helper(t)
    App(sf, st)
  case _ => t
}

def revFun(f:term):term = f match {
  case Fun(_, _, _) => revFun_helper(f)
  case _ =>
    Wrong
}

//features

class FunClass() {
  def LCId(x: String): term = mkFun(x, Var(x))

  def LCId(): term = LCId("x_")

  def LCTrue(t: String, f: String): term = mkFun(t, mkFun(f, Var(t)))

  def LCTrue(): term = LCTrue("tx1_", "tx2_")

  def LCFalse(t: String, f: String): term = mkFun(t, mkFun(f, Var(f)))

  def LCFalse(): term = LCFalse("fx1_", "fx2_")

  def LCIf(c: String, t: String, f: String): term = mkFun(c, mkFun(t, mkFun(f, App(App(Var(c), Var(t)), Var(f)))))

  def LCIf(): term = LCIf("c_", "t_", "f_")

  def LCAnd(a: String, b: String): term = mkFun(a, mkFun(b, App(App(Var(a), Var(b)), LCFalse("t_", "f_"))))

  def LCAnd(): term = LCAnd("a_", "b_")

  def LCOr(a: String, b: String): term = mkFun(a, mkFun(b, App(App(Var(a), LCTrue("t_", "f_")), Var(b))))

  def LCOr(): term = LCOr("a_", "b_")

  def LCNot(a: String): term = mkFun(a, App(App(App(LCIf("c_", "t_", "f_"), Var(a)), LCFalse("false_t", "false_f")), LCTrue("true_t", "true_f")))

  def LCNot(): term = LCNot("a_")

  def LCPair(a: String, b: String, s: String): term = mkFun(a, mkFun(b, mkFun(s, App(App(Var(s), Var(b)), Var(a)))))

  def LCPair(): term = LCPair("a_", "b_", "s_")

  def LCFirst(p: String): term = mkFun(p, App(Var(p), LCFalse("t_", "f_")))

  def LCFirst(): term = LCFirst("p_")

  def LCSecond(p: String): term = mkFun(p, App(Var(p), LCTrue("t_", "f_")))

  def LCSecond(): term = LCSecond("p_")
}

//evaluation

def eval_helper(t:term, env:Map[String,term]):term = {
  println("{")
  val res = t match {
    case Var(x) => env(x)
    case App(f, t1) => eval_helper(f, env) match {
      case Fun(m2, x2, t2) => eval_helper(t2, m2 + (x2 -> eval_helper(t1, env)))
      case _ =>
        println("Not a function : " + f)
        Wrong
    }
    case Fun(m, x, t) => Fun(m ++ env, x, t)
    case _ => t
  }
  println(res)
  println("}")
  res
}

def eval(t:term):term = {
  val m = EmptyMap()
  println(eval_helper(t, m))
  revFun(eval_helper(t, m))
}

//test cases

val f = new FunClass()

eval(mkFun("x", Var("x")))
//SimFun("x", Var("x"))
eval(App(mkFun("x", Var("x")), mkFun("x", Var("x"))))
//SimFun("x", Var("x"))

eval(App(App(f.LCTrue(), mkFun("x", Var("x"))), mkFun("y", Var("y"))))
//IDx
eval(App(App(mkFun("x", mkFun("y", Var("x"))), f.LCTrue()), f.LCFalse()))
//LCTrue
eval(App(App(App(f.LCIf(), f.LCTrue()), f.LCTrue()), f.LCFalse()))
//LCTrue

eval(App(App(f.LCAnd(), f.LCTrue()), f.LCTrue()))
//LCTrue
eval(App(App(f.LCAnd(), f.LCTrue()), f.LCFalse()))
//LCFalse
eval(App(App(f.LCAnd(), f.LCFalse("t", "f")), f.LCTrue()))
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