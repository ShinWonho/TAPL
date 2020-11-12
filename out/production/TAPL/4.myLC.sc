import scala.annotation.tailrec

// normal order base
// eta-reduction - optimizing before reducing
// make each term as a class -> if it reduces, same terms be changed -- possible?? //substitute
// if parameter doesn't use, not reduce the parameter
class myLC {

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

  trait state

  class Term(term: term) extends state {
    val t = term
  }

  object Normal extends state

  class Wrong(term: term) extends state {
    val t = term
  }

  def FV(t: term): Set[String] = {
    def FV_helper(s:Set[String], t:term):Set[String] = {
      t match {
        case t:Var => s + t.x
        case t:Fun => FV_helper(s, t.t)
        case t:App => FV_helper(FV_helper(s, t.f), t.p)
      }
    }

    FV_helper(Set(), t)
  }

  def substitute(t:term, from: String, to:term): term = {
    t match {
      case t:Var if t.x == from => to
      case t:Fun if t.x != from =>
        t.t = substitute(t.t, from, to)
        t
      case t:App =>
        t.f = substitute(t.f, from, to)
        t.p = substitute(t.p, from, to)
        t
      case _ => t
    }
  }

  def reduce(t: term): state = {
    t match {
      case _:Var => Normal

      case t:Fun => reduce(t.t) match {
        case state:Term =>
          t.t = state.t
          new Term(t)
        case _@state => state
      }

      case t:App =>
        reduce(t.f) match {
          case state:Wrong => state

          case state:Term =>
            t.f = state.t
            new Term(t)

          case Normal => t.f match {
            case f:Fun =>
              println("\t* substitution: " + concrete(f.t) + "[" + f.x + "->" + concrete(t.p) + "]")
              new Term(substitute(f.t, f.x, t.p))

            case _ => Normal
          }
        }
    }
  }

  def concrete(t: term): String = t match {
    case t:Var => t.x
    case t:Fun => "{ ^" + t.x + "." + concrete(t.t)+" }"
    case t:App => "( " + concrete(t.f) + " " + concrete(t.p) + " )"
  }

  @tailrec
  private def full_reduction(t: term, i: Int): Unit = {
    if (i > 100) return //max depth
    println("\t" + concrete(t))
    reduce(t) match {
      case w:Wrong => println("Wrong" + concrete(w.t))
      case Normal =>
      case t:Term => full_reduction(t.t, i + 1)
    }
  }

  var count = 0

  def run(t: term): Unit = {
    println("\ntest" + count + ":")
    full_reduction(t, 0)
    count += 1
  }

  def Var(s: String): Var = new Var(s)

  def Fun(s: String, term: term): term = new Fun(s, term)

  def App(f: term, p: term): term = new App(f, p)

  /* features */

  def LCId(): term = Fun("x", Var("x"))

  //boolean

  def LCTrue(): term = Fun("t", Fun("f", Var("t")))
  def LCFalse(): term = Fun("t", Fun("f", Var("f")))
  def LCIf(): term = Fun("c", Fun("t", Fun("f", App(App(Var("c"), Var("t")), Var("f")))))

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
  private def Church_helper(n:Int, t:term):term = n match {
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

  //test

  val param = App(App(LCId(), LCId()), LCId())
  run(App(Fun("x", App(Var("x"), Var("x"))), param))
//
//  run(LCId())
//  println("Id")
//  run(App(LCId(), LCId()))
//  println("Id")
//
//  run(App(App(LCTrue(), LCId()), LCId()))
//  println("Id")
//  run(App(App(Fun("x", Fun("y", Var("x"))), LCTrue()), LCFalse()))
//  println("LCTrue")
//  run(App(App(App(LCIf(), LCTrue()), LCTrue()), LCFalse()))
//  println("LCTrue")
//
//  println("\n<LCAND>")
//  run(App(App(LCAnd, LCTrue()), LCTrue()))
//  println("LCTrue")
//  run(App(App(LCAnd, LCTrue()), LCFalse()))
//  println("LCFalse")
//  run(App(App(LCAnd, LCFalse()), LCTrue()))
//  println("LCFalse")
//  run(App(App(LCAnd, LCFalse()), LCFalse()))
//  println("LCFalse")
//  println("\n<LCOR>")
//  run(App(App(LCOr(), LCTrue()), LCTrue()))
//  println("LCTrue")
//  run(App(App(LCOr(), LCTrue()), LCFalse()))
//  println("LCTrue")
//  run(App(App(LCOr(), LCFalse()), LCTrue()))
//  println("LCTrue")
//  run(App(App(LCOr(), LCFalse()), LCFalse()))
//  println("LCFalse")
//  println("\n<LCNOT>")
//  run(App(LCNot(), LCTrue()))
//  println("LCFalse")
//  run(App(LCNot(), LCFalse()))
//  println("LCTrue")
//
//  println("\n<LCPair>")
//  run(App(LCFirst(), App(App(LCPair(), LCTrue()), LCFalse())))
//  println("LCTrue")
//  run(App(LCSecond(), App(App(LCPair(), LCTrue()), LCFalse())))
//  println("LCFalse")
//
//  println("\n<LCSucc>")
//  run(Church(0))
//  println("LCZero")
//  run(App(LCSucc(),Church(0)))
//  println("LCOne")
//  run(App(LCSucc(), App(LCSucc(),Church(0))))
//  println("LCTwo")
//  run(App(LCSucc(), App(LCSucc(), App(LCSucc(),Church(0)))))
//  println("LCThree")
//  println("\n<LCPlus>")
//  run(App(App(LCPlus(), Church(0)), Church(0)))
//  println("LCZero")
//  run(App(App(LCPlus(), Church(0)), Church(1)))
//  println("LCOne")
//  run(App(App(LCPlus(), Church(3)), Church(4)))
//  println("LCSeven")
//  println("\n<LCMult>")
//  run(App(App(LCMult(), Church(1)), Church(2)))
//  println("LCTwo")
//  run(App(App(LCMult(), Church(2)), Church(4)))
//  println("LCEight")
//  println("\n<LCPower>")
//  run(App(App(LCPower(), Church(2)), Church(2)))
//  println("LCFour")
//  run(App(App(LCPower(), Church(3)), Church(2)))
//  println("LCNine")
//
//  run(App(LCIsZero(), Church(0)))
//  println("LCTrue")
//  run(App(LCIsZero(), Church(4)))
//  println("LCFalse")
//  run(App(LCPred(), Church(0)))
//  println("LCZero")
//  run(App(LCPred(), Church(4)))
//  println("LCFour")
//  run(App(App(LCSub(), Church(7)), Church(2)))
//  println("LCFive")
//  run(App(App(LCSub(), Church(3)), Church(5)))
//  println("LCZero")
//  run(App(App(LCEqual(), Church(0)), Church(0)))
//  println("LCTrue")
//  run(App(App(LCEqual(), Church(5)), Church(5)))
//  println("LCTrue")
//  run(App(App(LCEqual(), Church(3)), Church(8)))
//  println("LCFalse")
//  run(App(App(LCEqual(), Church(10)), Church(6)))
//  println("LCFalse")
}

println("hi")

val test = new myLC()