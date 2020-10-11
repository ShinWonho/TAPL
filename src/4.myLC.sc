import scala.annotation.tailrec

// normal order base
// eta-reduction - optimizing before reducing
// make each term as a class -> if it reduces, same terms be changed -- possible?? //substitute
// if parameter doesn't use, not reduce the parameter
class myLC {

  trait term

  class Var(s: String) extends term {
    val x = s
  }

  class Fun(name: String, term: term) extends term {
    val x = name
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

  object Wrong extends state//not used now, but later in num & bool

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
        case _:Term => new Term(t)
        case _@state => state
      }
      case t:App =>
        reduce(t.f) match {
          case Normal => t.f match {
            case func:Fun =>
              reduce(t.p) match {
                case Normal => new Term(substitute(func.t, func.x, t.p))
                case _:Term => new Term(t)
                case Wrong => Wrong
            }
            case _ => Wrong
          }
          case state:Term =>
            t.f = state.t
            new Term(t)
          case Wrong => Wrong
        }
    }
  }

  def concrete(t: term): String = t match {
    case t:Var => t.x + " "
    case t:Fun => "{ ^" + t.x + "." + concrete(t.t)+"} "
    case t:App => "( " + concrete(t.f) + concrete(t.p) + ") "
  }

  @tailrec
  private def full_reduction(t: term): Unit = {
    println("\t" + concrete(t))
    reduce(t) match {
      case Wrong => println("Wrong!")
      case Normal =>
      case t:Term => full_reduction(t.t)
    }
  }

  var count = 0

  def run(t: term): Unit = {
    println("\ntest" + count + ":")
    full_reduction(t)
  }

  def Var(s: String): Var = new Var(s)

  def Fun(s: String, term: term): term = new Fun(s, term)

  def App(f: term, p: term): term = new App(f, p)

  //test

  val t = App(Fun("x", {val x = Var("x"); x}), Fun("y", {val y = Var("y"); y}))

  run(t)

}

println("hi")

val test = new myLC()