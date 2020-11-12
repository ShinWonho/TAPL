//language features

trait term
case class Var(x:String) extends term
case class Fun(x:String, t:term) extends term
case class App(f:term, t:term) extends term
case object Wrong extends term

//functions

def EmptyMap(): Map[String, term] = Map[String, term]()

//features

def LCId():term = Fun("x", Var("x"))

def LCTrue():term = Fun("t", Fun("f", Var("t")))

def LCFalse():term = Fun("t", Fun("f", Var("f")))

def LCIf():term = Fun("l", Fun("m", Fun("n", App(App(Var("l"), Var("m")), Var("n")))))

def LCAnd():term = Fun("a", Fun("b", App(App(Var("a"), Var("b")), LCFalse())))

def LCOr(): term = Fun("a", Fun("b", App(App(Var("a"), LCTrue()), Var("b"))))

def LCNot(): term = Fun("a", App(App(App(LCIf(), Var("a")), LCFalse()), LCTrue()))

def LCPair():term = Fun("first", Fun("second", Fun("select", App(App(Var("select"), Var("second")), Var("first")))))

def LCFirst():term = Fun("pair", App(Var("pair"), LCFalse()))

def LCSecond():term = Fun("pair", App(Var("pair"), LCTrue()))

//evaluation

def eval_helper(t:term, env:Map[String,term]):term = t match {
  case Var(x) => env(x)
  case App(f, t1) => eval_helper(f, env) match {
    case Fun(x2, t2) => eval_helper(t2, env + (x2 -> eval_helper(t1, env)))
    case _ =>
      println("Not a function : " + f)
      Wrong
  }
  case _ => t
}

def eval(t:term):term = {
  val m = EmptyMap()
  eval_helper(t, m)
}

//test cases

eval(Fun("x", Var("x")))
//SimFun("x", Var("x"))
eval(App(Fun("x", Var("x")), Fun("x", Var("x"))))
//SimFun("x", Var("x"))

eval(App(App(LCTrue(), Fun("x", Var("x"))), Fun("y", Var("y"))))
//IDx
eval(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
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