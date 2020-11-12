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
  case Fun(m, x, t) => SimFun(x, revFun_helper(t))
  case App(f, t) =>
    val sf = revFun_helper(f)
    val st = revFun_helper(t)
    App(sf, st)
  case _ => t
}

def revFun(f:term):term = f match {
  case Fun(m, x, t) => revFun_helper(f)
  case _ =>
    Wrong
}

//features

def LCId():term = mkFun("x", Var("x"))

def LCTrue():term = mkFun("t", mkFun("f", Var("t")))

def LCFalse():term = mkFun("t", mkFun("f", Var("f")))

def LCIf():term = mkFun("l", mkFun("m", mkFun("n", App(App(Var("l"), Var("m")), Var("n")))))

def LCAnd():term = mkFun("a", mkFun("b", App(App(Var("a"), Var("b")), LCFalse())))

def LCOr(): term = mkFun("a", mkFun("b", App(App(Var("a"), LCTrue()), Var("b"))))

def LCNot(): term = mkFun("a", App(App(App(LCIf(), Var("a")), LCFalse()), LCTrue()))

def LCPair():term = mkFun("first", mkFun("second", mkFun("select", App(App(Var("select"), Var("second")), Var("first")))))

def LCFirst():term = mkFun("pair", App(Var("pair"), LCFalse()))

def LCSecond():term = mkFun("pair", App(Var("pair"), LCTrue()))

//evaluation

def eval_helper(t:term, env:Map[String,term]):term = t match {
  case Var(x) => env(x)
  case App(f, t1) => eval_helper(f, env) match {
    case Fun(m2, x2, t2) =>
      val v = eval_helper(t1, env)
      eval_helper(t2, m2 ++ env + (x2 -> v)) match {
        case Fun(m3, x3, t3) => Fun(m3 ++ m2 + (x2 -> v), x3, t3)
        case _@t3 =>
          println("Not a function : " + t3)
          Wrong
      }
    case _ =>
      println("Not a function : " + f)
      Wrong
  }
  case _ => t
}

def eval(t:term):term = {
  val m = EmptyMap()
  revFun(eval_helper(t, m))
}

//test cases

eval(mkFun("x", Var("x")))
//SimFun("x", Var("x"))
eval(App(mkFun("x", Var("x")), mkFun("x", Var("x"))))
//SimFun("x", Var("x"))

eval(App(App(LCTrue(), mkFun("x", Var("x"))), mkFun("y", Var("y"))))
//IDx
eval(App(App(mkFun("x", mkFun("y", Var("x"))), LCTrue()), LCFalse()))
//LCTrue
eval(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
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