import scala.annotation.tailrec

object nameless {

  trait term

  case class Var(x: String) extends term

  case class Fun(x: String, t: term) extends term

  case class App(f: term, p: term) extends term

  trait NLterm

  case class NLVar(i: Int) extends NLterm

  case class NLFun(t: NLterm) extends NLterm

  case class NLApp(f: NLterm, p: NLterm) extends NLterm

  def t2nl(t: term): NLterm = {
    def t2nl_helper(m: Map[String, Int], t: term): NLterm = t match {
      case Var(x) => NLVar(m(x))
      case Fun(x, t) => NLFun(t2nl_helper(m.foldLeft(Map[String, Int]())((m,p) => m + (p._1 -> (p._2 + 1))) + (x -> 0), t))
      case App(f, p) => NLApp(t2nl_helper(m, f), t2nl_helper(m, p))
    }

    t2nl_helper(Map(), t)
  }

  def shift(t: NLterm, place: Int): NLterm = shift(t, place, 0)
  def shift(t: NLterm, place: Int, bound: Int): NLterm = t match {
    case NLVar(i) => if (i < bound) NLVar(i) else NLVar(i + place)
    case NLFun(t) => NLFun(shift(t, place, bound + 1))
    case NLApp(f, p) => NLApp(shift(f, place, bound), shift(p, place, bound))
  }

  def substitution(t: NLterm, from: Int, to: NLterm): NLterm = t match {
    case NLVar(i) => if (i == from) to else NLVar(i)
    case NLFun(t) => NLFun(substitution(t, from + 1, shift(to, 1)))
    case NLApp(f, p) => NLApp(substitution(f, from, to), substitution(p, from, to))
  }

  def reduce(t: NLterm): NLterm = t match {
    case NLVar(_) => t
    case NLFun(t) => NLFun(reduce(t))
    case NLApp(f, p) => f match {
      case NLFun(t) =>
//        println("\t[0 -> " + concrete(shift(p, 1)) + "]" + concrete(t))
        shift(substitution(t, 0, shift(p, 1)), -1)
      case _ =>
        val tmp = reduce(f)
        if (tmp == f) NLApp(f, reduce(p)) else NLApp(tmp, p)
    }
  }

  def concrete(t: term): String = t match {
    case Var(x) => x
    case Fun(x, t) => "{^" + x + "." + concrete(t) + "}"
    case App(f, p) =>
      val res = concrete(f) + " "
      p match {
      case App(_, _) => res + "(" + concrete(p) + ")"
      case _ => res + concrete(p)
    }
  }

  def concrete(t: NLterm): String = t match {
    case NLVar(x) => "" + x
    case NLFun(t) => "{^." + concrete(t) + "}"
    case NLApp(f, p) =>
      val res = concrete(f) + " "
      p match {
        case NLApp(_, _) => res + "(" + concrete(p) + ")"
        case _ => res + concrete(p)
      }
  }
  
  @tailrec
  def full_reduce(t: NLterm, i: Int): NLterm = {
//    println("\t" + i + ": " + concrete(t))
    val res = reduce(t)
    if (t == res) {
      println("total step: " + i)
      res
    } else full_reduce(res, i+1)
  }

  def test(t: term): Unit = {
    println("ordinary: " + concrete(t))
    val nl = t2nl(t)
    println("nameless: " + concrete(nl))
    println("Normal form: " + concrete(full_reduce(nl, 0)))
    
  }

  def LCId(): term = Fun("x", Var("x"))

  //boolean

  def LCTrue(): term = Fun("t1", Fun("f1", Var("t1")))
  def LCFalse(): term = Fun("t", Fun("f", Var("f")))
  def LCIf(): term = Fun("c", Fun("t2", Fun("f2", App(App(Var("c"), Var("t2")), Var("f2")))))

  //boolean operation

  def LCAnd: term = Fun("a", Fun("b", App(App(Var("a"), Var("b")), LCFalse())))
  def LCOr(): term = Fun("a", Fun("b", App(App(Var("a"), LCTrue()), Var("b"))))
  def LCNot(): term = Fun("a", App(App(App(LCIf(), Var("a")), LCFalse()), LCTrue()))

  //pair

  def LCPair(): term = Fun("a", Fun("b", Fun("s", App(App(Var("s"), Var("b")), Var("a")))))
  def LCFirst(): term = Fun("p", App(Var("p"), LCFalse()))
  def LCSecond(): term = Fun("p", App(Var("p"), LCTrue()))

  //church numeral

  @tailrec
  def Church_helper(n:Int, t:term):term = n match {
    case 0 => t
    case _ => Church_helper(n - 1, App(Var("s"), t))
  }
  def Church(n:Int):term = Fun("s", Fun("z", Church_helper(n, Var("z"))))
  def LCSucc(): term = Fun("n", Fun("s", Fun("z", App(Var("s"), App(App(Var("n"), Var("s")), Var("z"))))))
  def LCPlus(): term = Fun("m", Fun("n", Fun("s", Fun("z", App(App(Var("m"), Var("s")), App(App(Var("n"), Var("s")), Var("z")))))))
  def LCMult(): term = Fun("m", Fun("n", App(App(Var("m"), App(LCPlus(), Var("n"))), Church(0))))
  def LCPower(): term = Fun("m", Fun("n", App(App(Var("n"), App(LCMult(), Var("m"))), Church(1))))
  def LCIsZero(): term = Fun("m", App(App(Var("m"),Fun("x", LCFalse())), LCTrue()))
  def LCZeroPair(): term = App(App(LCPair(), Church(0)), Church(0))
  def LCSuccPair(): term = Fun("p", App(App(LCPair(), App(LCSecond(), Var("p"))), App(LCSucc(), App(LCSecond(), Var("p")))))
  def LCPred(): term = Fun("m", App(LCFirst(), App(App(Var("m"), LCSuccPair()), LCZeroPair())))
  def LCSub(): term = Fun("m", Fun("n", App(App(Var("n"), LCPred()), Var("m"))))
  def LCEqual(): term = Fun("m", Fun("n", App(App(LCAnd, App(LCIsZero(), App(App(LCSub(), Var("m")), Var("n")))), App(LCIsZero(), App(App(LCSub(), Var("n")), Var("m"))))))

  //list

  def LCEmptyList(): term = Fun("c", Fun("n", Var("n")))
  def LCCons(): term = Fun("e", Fun("l", Fun("c", Fun("n", App(App(Var("c"), Var("e")), App(App(Var("l"), Var("c")), Var("n")))))))
  def LCHead(): term = Fun("l", App(App(Var("l"), LCTrue()), LCEmptyList()))
  def LCAlwaysFalse: term = Fun("c", Fun("n", LCFalse()))
  def LCIsNil(): term = Fun("l", App(App(Var("l"), LCAlwaysFalse), LCTrue()))
  def LCEmptyPair(): term = App(App(LCPair(), LCEmptyList()), LCEmptyList())
  def LCConsPair: term = Fun("e", Fun("p", App(App(LCPair(), App(LCSecond(), Var("p"))), App(App(LCCons(), Var("e")), App(LCSecond(), Var("p"))))))
  def LCPopFront(): term = Fun("l", App(LCFirst(), App(App(Var("l"), LCConsPair), LCEmptyPair())))
  def LCConsTail(): term = Fun("e", Fun("l", App(App(App(LCIf(), App(LCIsNil(), Var("l"))), App(App(LCCons(), Var("e")), LCEmptyList())), Var("l"))))
  def LCTail(): term = Fun("l", App(App(App(App(Var("l"), LCConsTail()), LCEmptyList()), LCTrue()), LCEmptyList()))

  def fix(): term = Fun("f", App(Fun("x", App(Var("f"), Fun("y", App(App(Var("x"), Var("x")), Var("y"))))), Fun("x", App(Var("f"), Fun("y", App(App(Var("x"), Var("x")), Var("y")))))))
  def fact(): term = Fun("f", Fun("n", App(App(App(LCIf(), App(LCIsZero(), Var("n"))), Church(1)), App(App(LCMult(), Var("n")), App(Var("f"), App(LCPred(), Var("n")))))))
  def LCfactorial(): term = App(fix(), fact())

  //test5
  test(App(App(LCTrue(), LCId()), LCId()))
  println("Id")
  test(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
  println("LCTrue")
  test(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
  println("LCTrue")

  //test8
  println("\n<LCAND>")
  test(App(App(LCAnd, LCTrue()), LCTrue()))
  println("LCTrue")
  test(App(App(LCAnd, LCTrue()), LCFalse()))
  println("LCFalse")
  test(App(App(LCAnd, LCFalse()), LCTrue()))
  println("LCFalse")
  test(App(App(LCAnd, LCFalse()), LCFalse()))
  println("LCFalse")
  println("\n<LCOR>")
  test(App(App(LCOr(), LCTrue()), LCTrue()))
  println("LCTrue")
  test(App(App(LCOr(), LCTrue()), LCFalse()))
  println("LCTrue")
  test(App(App(LCOr(), LCFalse()), LCTrue()))
  println("LCTrue")
  test(App(App(LCOr(), LCFalse()), LCFalse()))
  println("LCFalse")
  println("\n<LCNOT>")
  test(App(LCNot(), LCTrue()))
  println("LCFalse")
  test(App(LCNot(), LCFalse()))
  println("LCTrue")

  //test18
  println("\n<LCPair>")
  test(App(LCFirst(), App(App(LCPair(), LCTrue()), LCFalse())))
  println("LCTrue")
  test(App(LCSecond(), App(App(LCPair(), LCTrue()), LCFalse())))
  println("LCFalse")

  //test20
  println("\n<LCSucc>")
  test(Church(0))
  println("LCZero")
  test(App(LCSucc(),Church(0)))
  println("LCOne")
  test(App(LCSucc(), App(LCSucc(),Church(0))))
  println("LCTwo")
  test(App(LCSucc(), App(LCSucc(), App(LCSucc(),Church(0)))))
  println("LCThree")
  println("\n<LCPlus>")
  test(App(App(LCPlus(), Church(0)), Church(0)))
  println("LCZero")
  test(App(App(LCPlus(), Church(0)), Church(1)))
  println("LCOne")
  test(App(App(LCPlus(), Church(3)), Church(4)))
  println("LCSeven")
  println("\n<LCMult>")
  test(App(App(LCMult(), Church(1)), Church(2)))
  println("LCTwo")
  test(App(App(LCMult(), Church(2)), Church(4)))
  println("LCEight")
  println("\n<LCPower>")
  test(App(App(LCPower(), Church(2)), Church(2)))
  println("LCFour")
  test(App(App(LCPower(), Church(3)), Church(2)))
  println("LCNine")

  //test31
  println("\n<Eq/Sub>")
  test(App(LCIsZero(), Church(0)))
  println("LCTrue")
  test(App(LCIsZero(), Church(4)))
  println("LCFalse")
  test(App(LCPred(), Church(0)))
  println("LCZero")
  test(App(LCPred(), Church(4)))
  println("LCThree")
  test(App(App(LCSub(), Church(7)), Church(2)))
  println("LCFive")
  test(App(App(LCSub(), Church(3)), Church(5)))
  println("LCZero")
  test(App(App(LCEqual(), Church(0)), Church(0)))
  println("LCTrue")
  test(App(App(LCEqual(), Church(5)), Church(5)))
  println("LCTrue")
  test(App(App(LCEqual(), Church(3)), Church(8)))
  println("LCFalse")
  test(App(App(LCEqual(), Church(10)), Church(6)))
  println("LCFalse")

  println("\n<Recursion>")
  test(App(LCfactorial(), Church(2)))
  println("LCTwo")
  
  

}

val test = nameless