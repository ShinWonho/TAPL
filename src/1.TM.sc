import scala.annotation.tailrec
//language features

trait term
case object TmTrue extends term
case object TmFalse extends term
case object TmZero extends term
case object Wrong extends term
case class TmIf(TmCond:term, TmThen:term, TmElse:term) extends term
case class TmSucc(num:term) extends term
case class TmPrev(num:term) extends term
case class TmIsZero(num:term) extends term

//functions

@tailrec
def IsNumericVal(t:term) : term = t match {
  case TmZero => TmTrue
  case TmSucc(t) => IsNumericVal(t)
  case TmPrev(t) => IsNumericVal(t)
  case _ => TmFalse
}

def IsVal(t:term) : term = t match {
  case TmTrue => TmTrue
  case TmFalse => TmTrue
  case _@t => IsNumericVal(t)
}

//evaluation

def eval(t:term) : term = t match {
  case TmIf(t1, t2, t3) => eval(t1) match {
    case TmTrue => eval(t2)
    case TmFalse => eval(t3)
    case _ => Wrong
  }
  case TmSucc(t1) =>
    val ev = eval(t1)
    IsNumericVal(ev) match {
      case TmTrue => TmSucc(ev)
      case TmFalse => Wrong
    }
  case TmPrev(t1) =>
    val ev = eval(t1)
    IsNumericVal(ev) match {
      case TmTrue => ev match {
        case TmSucc(t_in) => t_in
        case _ => TmZero
      }
      case TmFalse => Wrong
    }
  case TmIsZero(t) => eval(t) match {
    case TmZero => TmTrue
    case _ => TmFalse
  }
  case _@t => t
}

//test cases

IsNumericVal(TmIf(TmPrev(TmZero), TmZero, TmFalse))
//TmFalse
IsNumericVal(TmZero)
//TmTrue
IsNumericVal(TmPrev(TmZero))
//TmTrue
IsNumericVal(TmPrev(TmPrev(TmSucc(TmSucc(TmSucc(TmZero))))))
//TmTrue
IsNumericVal(TmPrev(TmPrev(TmSucc(TmSucc(TmSucc(TmTrue))))))
//TmFalse

IsVal(TmIf(TmPrev(TmZero), TmZero, TmFalse))
//TmFalse
IsVal(TmZero)
//TmTrue
IsVal(TmPrev(TmPrev(TmSucc(TmSucc(TmSucc(TmZero))))))
//TmTrue
IsVal(TmPrev(TmPrev(TmSucc(TmSucc(TmSucc(TmTrue))))))
//TmFalse

eval(TmIf(TmPrev(TmZero), TmZero, TmFalse))
//TmWrong
eval(TmPrev(TmZero))
//TmZero
eval(TmSucc(TmPrev(TmZero)))
//TmSucc(TmZero)
eval(TmIf(TmIsZero(TmSucc(TmPrev(TmZero))), TmTrue, TmFalse))
//TmFalse
eval(TmIf(TmTrue, TmTrue, Wrong))
//TmTrue
eval(TmIf(TmZero, TmTrue, TmFalse))
//Wrong
eval(TmSucc(Wrong))
//Wrong
eval(TmSucc(TmTrue))
//Wrong
eval(TmPrev(TmFalse))
//Wrong
eval(TmIsZero(TmTrue))
//TmFalse
eval(TmIsZero(TmSucc(TmZero)))
//TmFalse