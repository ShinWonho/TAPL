import scala.annotation.tailrec

object myLC {

  trait term

  class Var(s: String) extends term {
    var x = s
  }

  class Fun(name: String, term: term) extends term {
    var x = name
    var t = term
  }

  class App(func: term, param: term) extends term {
    var f = func
    var p = param
  }

  class param(term: term) extends term {
    var in = term
  }

  trait state

  object Reducible extends state

  object Normal extends state

  var alpha = 0

  def alpha_conversion(t: Fun): Fun = {
    val from = t.x
    val to = t.x + alpha
    def alpha_conversion_helper(t: term): Unit = t match {
      case t: Var if t.x == from => t.x = to
      case t: Fun if t.x != from => alpha_conversion_helper(t.t)
      case t: App => alpha_conversion_helper(t.f); alpha_conversion_helper(t.p)
      case t: param => alpha_conversion_helper(t.in)
      case _ =>
    }
    println("\talpha conversion: " + concrete(t) + "[" + from + "->" + to + "]")
    alpha_conversion_helper(t.t)
    t.x = to
    println("\t                ->" + concrete(t))
    alpha += 1
    t
  }

  def contains(t: term, s: String): Boolean = {
    def FV(set: Set[String], t: term): Set[String] = t match {
      case t: Var => set + t.x
      case t: Fun =>
        FV(set, t.t)
        set - t.x
      case t: App => FV(FV(set, t.f), t.p)
      case t: param => FV(set, t.in)
    }
    val fv = FV(Set(), t)
    fv.contains(s)
  }

  def substitute(t: term, from: String, to: term): term = t match {
    case t: Var => if (t.x == from) to else t
    case t: Fun if contains(to, t.x) => substitute(alpha_conversion(t), from, to)
    case t: Fun if t.x == from => t
    case t: Fun =>
      t.t = substitute(t.t, from, to)
      t
    case t: App =>
      t.f = substitute(t.f, from, to)
      t.p = substitute(t.p, from, to)
      t
    case t: param =>
      t.in = substitute(t.in, from, to)
      t
  }

  def doApp(f: Fun, p: term): term = {
    println("\tApp: " + concrete(f) + "\n\t    " + concrete(p))
    if (contains(p, f.x)) alpha_conversion(f)
    println("\tsubstitution: " + concrete(f.t) + "[" + f.x + "->" + concrete(p) + "]")
    substitute(f.t, f.x, new param(p))
  }

  def reduceApp(a: App): (term, state) = {
    val tpl = reduce(a.f)
    a.f = tpl._1
    tpl._2 match {
      case Reducible => (a, Reducible)
      case Normal =>
        val tpl = reduce(a.p)
        a.p = tpl._1
        (a, tpl._2)
    }
  }

  def deepcopy(t: Fun): Fun = deepcopy(t: term) match {
    case t: Fun => t
  }

  def deepcopy(t: term): term = t match {
    case t: Var => new Var(t.x)
    case t: Fun => new Fun(t.x, deepcopy(t.t))
    case t: App => new App(deepcopy(t.f), deepcopy(t.p))
    case t: param => new param(deepcopy(t.in))
  }

  @tailrec
  def peel(p: param): term = p.in match {
    case p: param => peel(p)
    case t => t
  }

  def reduce(t: term): (term, state) = {
    var res: (term, state) = (t, Normal)
    //    println("\t\treduce begin (" + concrete(t) + ")")
    t match {
      case t: Var => res = (t, Normal)
      case t: Fun =>
        val tpl = reduce(t.t)
        t.t = tpl._1
        res = (t, tpl._2)
      case t: App => t.f match {
        case f: Fun => res = (doApp(f, t.p), Reducible)
        case p: param => peel(p) match {
          case f: Fun => res = (doApp(deepcopy(f), t.p), Reducible)
          case _ => res = reduceApp(t)
        }
        case _ => res = reduceApp(t)
      }
      case t: param =>
        t.in = peel(t)
        val tpl = reduce(t.in)
        t.in = tpl._1
        tpl._2 match {
          case Normal =>
            tpl._1 match {
              case _: Fun => res = (deepcopy (tpl._1), Normal)
              case _ => res = (t, Normal)
            }
          case Reducible => res = (t, Reducible)
        }
    }
    //    println("\t\treduce end (" + concrete(t) + ")")
    res
  }

  var cnt = 0
  def run(t: term): Unit = {
    alpha = 0
    var reduce_step = 0
    @tailrec
    def run_helper(t: term): Unit = {
      if (reduce_step > 300) return
      println(reduce_step + ":\t" + concrete(t))
      reduce_step += 1
      val tpl = reduce(t)
      tpl._2 match {
        case Normal => println("@Normal form: " + concrete(clear(t)))
        case Reducible => run_helper(tpl._1)
      }
    }
    println("\ntest" + cnt + ":")
    run_helper(t)
    cnt += 1
  }

  def concrete(t: term): String = t match {
    case t: Var => t.x
    case t: Fun => "{^"+t.x+"."+concrete(t.t)+"}"
    case t: App =>
      val res = concrete(t.f) + " "
      t.p match {
        case p: App => res + "(" + concrete(p) + ")"
        case _ => res + concrete(t.p)
      }
    case t: param => "<" + concrete(t.in) + ">"
  }

  def clear(t: term): term = t match {
    case t: param => clear(t.in)
    case t: Fun =>
      t.t = clear(t.t)
      t
    case t: App =>
      t.f = clear(t.f)
      t.p = clear(t.p)
      t
    case _ => t
  }

  def Var(s: String): term = new Var(s)
  def Fun(s: String, t: term): term = new Fun(s, t)
  def App(f: term, t: term): term = new App(f, t)

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


  //  run(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
  //  run(App(Fun("y", {val a = new Var("y"); App(a, a)}), App(App(App(LCIf(), LCTrue()), LCId()), LCFalse())))

  val x1 = Var("x")
  val x2 = Var("x")
  val x3 = Var("x")
  val y1 = Var("y")
  val y2 = Var("y")
  val z = Var("z")
  val a = Var("a")
  //check alpha-conversion
  //test0
  run(App(Fun("x", Fun("x", Var("x"))), LCTrue()))
  println(concrete(LCId()))//shadowing ok
  run(App(Fun("x", App(Fun("x", Var("x")), App(x1, x1))), LCTrue()))
  println()
  run(App(Fun("x", Var("x")), Fun("x", Var("x"))))//no alpha conversion

  //test3
  run(LCId())
  println("Id")
  run(App(LCId(), LCId()))
  println("Id")

  //test5
  run(App(App(LCTrue(), LCId()), LCId()))
  println("Id")
  run(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
  println("LCTrue")
  run(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
  println("LCTrue")

  //test8
  println("\n<LCAND>")
  run(App(App(LCAnd, LCTrue()), LCTrue()))
  println("LCTrue")
  run(App(App(LCAnd, LCTrue()), LCFalse()))
  println("LCFalse")
  run(App(App(LCAnd, LCFalse()), LCTrue()))
  println("LCFalse")
  run(App(App(LCAnd, LCFalse()), LCFalse()))
  println("LCFalse")
  println("\n<LCOR>")
  run(App(App(LCOr(), LCTrue()), LCTrue()))
  println("LCTrue")
  run(App(App(LCOr(), LCTrue()), LCFalse()))
  println("LCTrue")
  run(App(App(LCOr(), LCFalse()), LCTrue()))
  println("LCTrue")
  run(App(App(LCOr(), LCFalse()), LCFalse()))
  println("LCFalse")
  println("\n<LCNOT>")
  run(App(LCNot(), LCTrue()))
  println("LCFalse")
  run(App(LCNot(), LCFalse()))
  println("LCTrue")

  //test18
  println("\n<LCPair>")
  run(App(LCFirst(), App(App(LCPair(), LCTrue()), LCFalse())))
  println("LCTrue")
  run(App(LCSecond(), App(App(LCPair(), LCTrue()), LCFalse())))
  println("LCFalse")

  //test20
  println("\n<LCSucc>")
  run(Church(0))
  println("LCZero")
  run(App(LCSucc(),Church(0)))
  println("LCOne")
  run(App(LCSucc(), App(LCSucc(),Church(0))))
  println("LCTwo")
  run(App(LCSucc(), App(LCSucc(), App(LCSucc(),Church(0)))))
  println("LCThree")
  println("\n<LCPlus>")
  run(App(App(LCPlus(), Church(0)), Church(0)))
  println("LCZero")
  run(App(App(LCPlus(), Church(0)), Church(1)))
  println("LCOne")
  run(App(App(LCPlus(), Church(3)), Church(4)))
  println("LCSeven")
  println("\n<LCMult>")
  run(App(App(LCMult(), Church(1)), Church(2)))
  println("LCTwo")
  run(App(App(LCMult(), Church(2)), Church(4)))
  println("LCEight")
  println("\n<LCPower>")
  run(App(App(LCPower(), Church(2)), Church(2)))
  println("LCFour")
  run(App(App(LCPower(), Church(3)), Church(2)))
  println("LCNine")

  //test31
  println("\n<Eq/Sub>")
  run(App(LCIsZero(), Church(0)))
  println("LCTrue")
  run(App(LCIsZero(), Church(4)))
  println("LCFalse")
  run(App(LCPred(), Church(0)))
  println("LCZero")
  run(App(LCPred(), Church(4)))
  println("LCFour")
  //    run(App(App(LCSub(), Church(7)), Church(2)))
  println("LCFive")
  //    run(App(App(LCSub(), Church(3)), Church(5)))
  println("LCZero")
  //    run(App(App(LCEqual(), Church(0)), Church(0)))
  println("LCTrue")
  //    run(App(App(LCEqual(), Church(5)), Church(5)))
  println("LCTrue")
  //    run(App(App(LCEqual(), Church(3)), Church(8)))
  println("LCFalse")
  //    run(App(App(LCEqual(), Church(10)), Church(6)))
  println("LCFalse")

  println("\n<Recursion>")
  run(App(LCfactorial(), Church(2)))
  println("LCTwo")

}

val ml = myLC