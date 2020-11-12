import scala.annotation.tailrec

object TypedLC extends App{

  trait Type

  object UnitType extends Type

  case class Arrow(param_type: Type, body_type: Type) extends Type

  case object BoolType extends Type

  case object NumType extends Type

  case class RecType(l: List[Type]) extends Type

  case class VarType(m: Map[String, Type]) extends Type

  case class ListType(t: Type) extends Type
  
  trait Term

  case object UnitTerm extends Term

  case class NumV(n: Int) extends Term

  case class BoolV(b: Boolean) extends Term
  
  case class Seq(t1: Term, t2: Term) extends Term

  case class Var(x: String) extends Term

  case class Fun(x: String, x_type: Type,  t: Term) extends Term

  case class App(f: Term, p: Term) extends Term

  case class If(b: Term, t: Term, e: Term) extends Term

  case class As(t: Term, ty: Type) extends Term

  case class Rec(l: List[Term]) extends Term

  case class Bind(p: RecPat, r: Term, t: Term) extends Term

  case class Tag(x: String, t: Term, ty: VarType) extends Term

  case class Case(t: Term, m: Map[String, (String, Term)]) extends Term

  case class IsZero(t: Term) extends Term

  case class Pred(t: Term) extends Term

  case class Mult(t1: Term, t2: Term) extends Term

  case class Fix(t: Term) extends Term
  
  case class Nil(ty: Type) extends Term
  
  case class Cons(ty: Type, h: Term, t: Term) extends Term

  case class IsNil(ty: Type, l: Term) extends Term
  
  case class Head(ty: Type, l: Term) extends Term
  
  case class Tail(ty: Type, l: Term) extends Term

  trait NLTerm
  
  case class NLSeq(t1: NLTerm, t2: NLTerm) extends NLTerm

  case class NLVar(i: Int) extends NLTerm

  case class NLFun(t: NLTerm) extends NLTerm with NLValue

  case class NLApp(f: NLTerm, p: NLTerm) extends NLTerm

  case class NLIf(b: NLTerm, t: NLTerm, e: NLTerm) extends NLTerm

  case class NLAs(t: NLTerm, ty: Type) extends NLTerm

  abstract class NLRec(list: List[NLTerm]) extends NLTerm {
    val l: List[NLTerm] = list
  }

  case class NLRecT(lt: List[NLTerm]) extends NLRec(lt)

  case class NLPat(x: String) extends NLTerm

  case class NLBind(p: RecPat, r: NLTerm, t: NLTerm) extends NLTerm

  abstract class NLTag(name: String, term: NLTerm) extends NLTerm {
    val x: String = name
    val t: NLTerm = term
  }

  case class NLTagT(xt: String, tt: NLTerm) extends NLTag(xt, tt)

  case class NLCase(t: NLTerm, m: Map[String, (String, NLTerm)]) extends NLTerm

  case class NLIsZero(t: NLTerm) extends NLTerm

  case class NLPred(t: NLTerm) extends NLTerm

  case class NLMult(t1: NLTerm, t2: NLTerm) extends NLTerm

  case class NLFix(t: NLTerm) extends NLTerm

  abstract class NLCons(hc: NLTerm, tc: NLTerm) extends NLTerm {
    val h: NLTerm = hc
    val t: NLTerm = tc
  }

  case class NLConsT(ht: NLTerm, tt: NLTerm) extends NLCons(ht, tt)

  case class NLIsNil(l: NLTerm) extends NLTerm

  case class NLHead(l: NLTerm) extends NLTerm

  case class NLTail(l: NLTerm) extends NLTerm

  trait NLValue extends NLTerm

  case object NLUnitTerm extends NLValue

  case class NLNumV(n: Int) extends NLValue

  case class NLBoolV(b: Boolean) extends NLValue

  case class NLRecV(lv: List[NLTerm]) extends NLRec(lv) with NLValue

  case class NLTagV(xv: String, tv: NLTerm) extends NLTag(xv, tv) with NLValue

  case object NLNil extends NLTerm with NLValue

  case class NLConsV(hv: NLTerm, tv: NLTerm) extends NLCons(hv, tv) with NLValue

  trait Pattern

  case class RecPat(l: List[String]) extends Pattern
  
//  case class VarPat(x: List[String], l: List[String]) extends Pattern

  def t2nl(t: Term): NLTerm = t2nl(Map(), t)
  def t2nl(m: Map[String, Int], l: List[Term]): List[NLTerm] = l.foldRight(List[NLTerm]())((e, l) => t2nl(m, e) :: l)
  def t2nl(m: Map[String, Int], t: Term): NLTerm = t match {
    case UnitTerm => NLUnitTerm
    case Seq(t1, t2) => NLSeq(t2nl(m, t1), t2nl(m, t2))
    case Var(x) => m.get(x) match {
      case Some(v) => NLVar(v)
      case None => NLPat(x)
    }
    case Fun(x, _, t) => NLFun(t2nl(m.foldLeft(Map[String, Int]())((m, p) => m + (p._1 -> (p._2 + 1))) + (x -> 0), t))
    case App(f, p) => NLApp(t2nl(m, f), t2nl(m, p))
    case NumV(n) => NLNumV(n)
    case BoolV(b) => NLBoolV(b)
    case If(c, t, e) => NLIf(t2nl(m, c), t2nl(m, t), t2nl(m, e))
    case As(t, ty) => NLAs(t2nl(m, t), ty)
    case Rec(l) => NLRecT(t2nl(m, l))
    case Bind(p, r, t) => NLBind(p, t2nl(m, r), t2nl(m, t))
    case Tag(x, t, _) => NLTagT(x, t2nl(m, t))
    case Case(t, cm) => NLCase(t2nl(m, t), cm.foldLeft(Map[String, (String, NLTerm)]())((cm, e) => cm + (e._1 -> (e._2._1, t2nl(m, e._2._2)))))
    case IsZero(t) => NLIsZero(t2nl(m, t))
    case Pred(t) => NLPred(t2nl(m, t))
    case Mult(t1, t2) => NLMult(t2nl(m, t1), t2nl(m, t2))
    case Fix(t) => NLFix(t2nl(m, t))
    case Nil(_) => NLNil
    case Cons(_, h, t) => NLConsT(t2nl(m, h), t2nl(m, t))
    case IsNil(_, l) => NLIsNil(t2nl(l))
    case Head(_, t) => NLHead(t2nl(m, t))
    case Tail(_, t) => NLTail(t2nl(m, t))
  }

  def shift(t: NLTerm, place: Int): NLTerm = shift(t, place, 0)
  def shift(l: List[NLTerm], place: Int, bound: Int): List[NLTerm] = l.foldRight(List[NLTerm]())((e, l) => shift(e, place, bound) :: l)
  def shift(t: NLTerm, place: Int, bound: Int): NLTerm = t match {
    case NLUnitTerm => NLUnitTerm
    case NLSeq(t1, t2) => NLSeq(shift(t1, place, bound), shift(t2, place, bound))
    case NLVar(i) => if (i < bound) NLVar(i) else NLVar(i + place)
    case NLFun(t) => NLFun(shift(t, place, bound + 1))
    case NLApp(f, p) => NLApp(shift(f, place, bound), shift(p, place, bound))
    case NLNumV(n) => NLNumV(n)
    case NLBoolV(b) => NLBoolV(b)
    case NLIf(c, t, e) => NLIf(shift(c, place, bound), shift(t, place, bound), shift(e, place, bound))
    case NLAs(t, ty) => NLAs(shift(t, place, bound), ty)
    case NLRecT(l) => NLRecT(shift(l, place, bound))
    case NLRecV(l) => NLRecV(shift(l, place, bound))
    case NLPat(x) => NLPat(x)
    case NLBind(p, r, t) => NLBind(p, shift(r, place, bound), shift(t, place, bound))
    case NLTagT(x, t) => NLTagT(x, shift(t, place, bound))
    case NLTagV(x, t) => NLTagV(x, shift(t, place, bound))
    case NLCase(t, m) => NLCase(shift(t, place, bound), m.foldLeft(Map[String, (String, NLTerm)]())((cm, e) => cm + (e._1 -> (e._2._1, shift(e._2._2, place, bound)))))
    case NLIsZero(t) => NLIsZero(shift(t, place, bound))
    case NLPred(t) => NLPred(shift(t, place, bound))
    case NLMult(t1, t2) => NLMult(shift(t1, place, bound), shift(t2, place, bound))
    case NLFix(t) => NLFix(shift(t, place, bound))
    case NLNil => NLNil
    case NLConsT(h, t) => NLConsT(shift(h, place, bound), shift(t, place, bound))
    case NLConsV(h, t) => NLConsV(shift(h, place, bound), shift(t, place, bound))
    case NLIsNil(l) => NLIsNil(shift(l, place, bound))
    case NLHead(l) => NLHead(shift(l, place, bound))
    case NLTail(l) => NLTail(shift(l, place, bound))
  }

  def NLsubstitution(t: NLTerm, to: NLTerm): NLTerm = NLsubstitution(t, 0, to)
  def NLsubstitution(l: List[NLTerm], from: Int, to: NLTerm): List[NLTerm] = l.foldRight(List[NLTerm]())((e, l) => NLsubstitution(e, from, to) :: l)
  def NLsubstitution(t: NLTerm, from: Int, to: NLTerm): NLTerm = t match {
    case NLSeq(t1, t2) => NLSeq(NLsubstitution(t1, from, to), NLsubstitution(t2, from, to))
    case NLVar(i) => if (i == from) to else NLVar(i)
    case NLFun(t) => NLFun(NLsubstitution(t, from + 1, shift(to, 1)))
    case NLApp(f, p) => NLApp(NLsubstitution(f, from, to), NLsubstitution(p, from, to))
    case NLIf(c, t, e) => NLIf(NLsubstitution(c, from, to), NLsubstitution(t, from, to), NLsubstitution(e, from, to))
    case NLAs(t, ty) => NLAs(NLsubstitution(t, from, to), ty)
    case NLRecT(l) => NLRecT(NLsubstitution(l, from, to))
    case NLPat(x) => NLPat(x)
    case NLBind(p, r, t) => NLBind(p, NLsubstitution(r, from, to), NLsubstitution(t, from, to))
    case NLTagT(x, t) => NLTagT(x, NLsubstitution(t, from, to))
    case NLCase(t, m) => NLCase(NLsubstitution(t, from, to), m.foldLeft(Map[String, (String, NLTerm)]())((cm, e) => cm + (e._1 -> (e._2._1, NLsubstitution(e._2._2, from, to)))))
    case NLIsZero(t) => NLIsZero(NLsubstitution(t, from, to))
    case NLPred(t) => NLPred(NLsubstitution(t, from, to))
    case NLMult(t1, t2) => NLMult(NLsubstitution(t1, from, to), NLsubstitution(t2, from, to))
    case NLFix(t) => NLFix(NLsubstitution(t, from, to))
    case NLNil => NLNil
    case NLConsT(h, t) => NLConsT(NLsubstitution(h, from, to), NLsubstitution(t, from, to))
    case NLConsV(h, t) => NLConsV(NLsubstitution(h, from, to), NLsubstitution(t, from, to))
    case NLIsNil(l) => NLIsNil(NLsubstitution(l, from, to))
    case NLHead(l) => NLHead(NLsubstitution(l, from, to))
    case NLTail(l) => NLTail(NLsubstitution(l, from, to))
    case _: NLValue => t
  }

  def substitution(l: List[NLTerm], from: String, to: NLTerm): List[NLTerm] = l.foldRight(List[NLTerm]())((e, l) => substitution(e, from, to) :: l)
  def substitution(t: NLTerm, from: String, to: NLTerm): NLTerm = t match {
    case NLSeq(t1, t2) => NLSeq(substitution(t1, from, to), substitution(t2, from, to))
    case NLVar(i) => NLVar(i)
    case NLFun(t) => NLFun(substitution(t, from + 1, shift(to, 1)))
    case NLApp(f, p) => NLApp(substitution(f, from, to), substitution(p, from, to))
    case NLIf(c, t, e) => NLIf(substitution(c, from, to), substitution(t, from, to), substitution(e, from, to))
    case NLAs(t, ty) => NLAs(substitution(t, from, to), ty)
    case NLRecT(l) => NLRecT(substitution(l, from, to))
    case NLPat(x) => if (x == from) to else NLPat(x)
    case NLBind(p, r, t) => if (p.l.contains(from)) NLBind(p, r, t) else NLBind(p, substitution(r, from, to), substitution(t, from, to))
    case NLTagT(x, t) => NLTagT(x, substitution(t, from, to))
    case NLCase(t, m) => if (m.forall(e => e._2._1 != from))
        NLCase(substitution(t, from, to), m.foldLeft(Map[String, (String, NLTerm)]())((cm, e) => cm + (e._1 -> (e._2._1, substitution(e._2._2, from, to)))))
                          else NLCase(t, m)
    case NLIsZero(t) => NLIsZero(substitution(t, from, to))
    case NLPred(t) => NLPred(substitution(t, from, to))
    case NLMult(t1, t2) => NLMult(substitution(t1, from, to), substitution(t2, from, to))
    case NLFix(t) => NLFix(substitution(t, from, to))
    case NLNil => NLNil
    case NLConsT(h, t) => NLConsT(substitution(h, from, to), substitution(t, from, to))
    case NLConsV(h, t) => NLConsV(substitution(h, from, to), substitution(t, from, to))
    case NLIsNil(l) => NLIsNil(substitution(l, from, to))
    case NLHead(l) => NLHead(substitution(l, from, to))
    case NLTail(l) => NLTail(substitution(l, from, to))
    case _: NLValue => t
  }

//  def isWellFormed(t: NLTerm): Boolean = isWellFormed(t, -1)
//
//  def isWellFormed(t: NLTerm, upper: Int): Boolean = t match {
//    case _: NLValue => true
//    case NLSeq(t1, t2) => isWellFormed(t1, upper) && isWellFormed(t2, upper)
//    case NLVar(i) => i <= upper
//    case NLFun(t) => isWellFormed(t, upper + 1)
//    case NLApp(f, p) => isWellFormed(f, upper) && isWellFormed(p, upper)
//    case NLIf(c, t, e) => isWellFormed(c, upper) && isWellFormed(t, upper) && isWellFormed(e, upper)
//    case NLAs(t, _) => isWellFormed(t, upper)
//    case NLRecT(l) => l.forall(isWellFormed(_, upper))
//    case NLPat(_) => true
//    case NLBind(_, r, t) => isWellFormed(r, upper) && isWellFormed(t)//cannot check the length!
//    case NLTagT(_, t) => isWellFormed(t, upper)
//    case NLCase(t, m) => isWellFormed(t) && m.forall(e => isWellFormed(e._2._2, upper))
//    case NLIsZero(t) => isWellFormed(t)
//    case NLPred(t) => isWellFormed(t)
//    case NLMult(t1, t2) => isWellFormed(t1) && isWellFormed(t2)
//    case NLFix(t) => isWellFormed(t)
//  }

  def isVal(t: NLTerm): Boolean = t match {
    case _: NLValue => true
    case _ => false
  }

  def reduce_rec_list(l: List[NLTerm]): List[NLTerm] = reduce_rec_list_helper(List(), l)
  @tailrec
  def reduce_rec_list_helper(res: List[NLTerm], l: List[NLTerm]): List[NLTerm] = l match {
    case h :: t => if (isVal(h)) reduce_rec_list_helper(res :+ h, t) else res :+ reduce(h) :++ t
    case _ => res
  }

  def reduce(t: NLTerm): NLTerm = t match {
    case NLSeq(t1, t2) => if (isVal(t1)) t2 else NLSeq(reduce(t1), t2)
    case NLVar(x) => NLVar(x)
    case NLFun(b) => NLFun(reduce(b))
    case NLApp(f, p) => f match {
      case NLFun(t) =>
//        println("\t\t[0 -> " + concrete(shift(p, 1)) + "]" + concrete(t))
        shift(NLsubstitution(t, shift(p, 1)), -1)
      case f => NLApp(reduce(f), p)
    }
    case NLIf(c, t, e) => c match {
      case NLBoolV(b) => if (b) t else e
      case _ => NLIf(reduce(c), t, e)
    }
    case NLAs(t, ty) => if (isVal(t)) t else NLAs(reduce(t), ty)
    case NLRecT(l) => if (l.forall(isVal)) NLRecV(l match {case l: List[NLValue] => l}) else NLRecT(reduce_rec_list(l))
    case NLPat(x) => NLPat(x)
    case NLBind(p, r, t) => r match {
      case r: NLRecV =>
        val from_to = p.l zip r.l
        from_to.foldLeft(t)((t, e) => substitution(t, e._1, e._2))
      case _ => NLBind(p, reduce(r), t)
    }
    case NLTagT(x, t) => t match {
      case t: NLValue => NLTagV(x, t)
      case _ => NLTagT(x, reduce(t))
    }
    case NLCase(t1, m) => t1 match {
      case NLTagV(x, v) => m.get(x) match {
        case None => throw new RuntimeException("No matching case at " + concrete(t))
        case Some(e) => substitution(e._2, e._1, v)
      }
      case _ => NLCase(reduce(t1), m)
    }
    case NLIsZero(t) => t match {
      case NLNumV(n) => NLBoolV(n == 0)
      case _ => NLIsZero(reduce(t))
    }
    case NLPred(t) => t match {
      case NLNumV(n) => NLNumV(n - 1)
      case _ => NLPred(reduce(t))
    }
    case NLMult(t1, t2) => t1 match {
      case NLNumV(n1) => t2 match {
        case NLNumV(n2) => NLNumV(n1 * n2)
        case _ => NLMult(t1, reduce(t2))
      }
      case _ => NLMult(reduce(t1), t2)
    }
    case NLFix(t) => t match {
      case NLFun(t1) =>
        //          println("\t\t[0 -> " + concrete(shift(NLFix(t), 1)) + "]" + concrete(t1))
        shift(NLsubstitution(t1, shift(NLFix(t), 1)), -1)
      case f => NLFix(reduce(f))
    }
    case NLConsT(h, t) => h match {
      case v: NLValue => t match {
        case v2: NLValue => NLConsV(v, v2)
        case _ => NLConsT(v, reduce(t))
      }
      case _ => NLConsT(reduce(h), t)
    }
    case NLIsNil(l) => l match {
      case _: NLCons => NLBoolV(false)
      case NLNil => NLBoolV(true)
      case _ => NLIsNil(reduce(l))
    }
    case NLHead(l) => l match {
      case NLConsV(v, _) => v
      case _ => NLHead(reduce(l))
    }
    case NLTail(l) => l match {
      case NLConsV(_, v) => v
      case _ => NLTail(reduce(l))
    }
    case _: NLValue => t
  }

  def concrete(ty: Type): String = ty match {
    case UnitType => "Unit"
    case Arrow(p, t) => concrete(p) + "->" + concrete(t)
    case NumType => "Num"
    case BoolType => "Bool"
    case RecType(l) => l.foldLeft("{ ")((s, e) =>s + concrete(e) + " ") + "}"
    case VarType(l) => l.foldLeft("< ")((s, e) =>s + e._1 + ": " + concrete(e._2) + " ") + ">"
    case ListType(ty) => "List[" + concrete(ty) + "]"
  }

  def concrete(t: Term): String = concrete(t2nl(t), 1)

  def concrete(t: NLTerm): String = concrete(t, 0)

  def concrete(t: NLTerm, numtap: Int): String = {
    val enter = "\n\t" + ("  " * numtap)
    t match {
      case NLUnitTerm => "unit"
      case NLNumV(n) => "" + n
      case NLBoolV(b) => if (b) "true" else "false"
      case NLSeq(t1, t2) => concrete(t1, numtap) + ";" + enter + concrete(t2, numtap)
      case NLVar(x) => x + "_"
      case NLFun(t) => t match {
        case NLFun(_) => "^." + concrete(t, numtap)
        case _ => "^." + enter + "  " + concrete(t, numtap + 1)
      }
      case NLApp(f, p) =>
        val res = concrete(f, numtap) + " "
        p match {
          case NLApp(_, _) => res + "(" + concrete(p, numtap) + ")"
          case _ => res + concrete(p, numtap)
        }
      case NLIf(c, t, e) => "if (" + concrete(c, numtap) + ")" + enter + "  " + concrete(t, numtap + 1) + enter + "else" + enter + "  " + concrete(e, numtap + 1)
      case NLAs(t, ty) => concrete(t, numtap) + " as " + concrete(ty)
      case t: NLRec => t.l.foldLeft("Rec")((s, e) =>s + enter + "  " + concrete(e, numtap + 1))
      case NLPat(x) => x
      case NLBind(p, r, t) => p.l.foldLeft("Bind ")((s, e) => s + e + ", ") + "->" + concrete(r, numtap) + enter + "  " + "=>" +  concrete(t, numtap)
      case t: NLTag => "<" + t.x + ": " + concrete(t.t, numtap) + ">"
      case NLCase(t, m) => "case (" + concrete(t, numtap) + ") of " +  m.foldLeft("")((s, e) => s + enter + "  " + e._1 + ": " + e._2._1 + " -> " + concrete(e._2._2, numtap + 1) + ";")
      case NLIsZero(t) => concrete(t, numtap) + "?"
      case NLPred(t) => t match {
        case NLNumV(n) => n + "'"
        case NLPred(_) => concrete(t, numtap) + "'"
        case _ => "(" + concrete(t, numtap) + ")--"
      }
      case NLMult(t1, t2) => concrete(t1, numtap) + "*" + concrete(t2, numtap)
      case NLFix(t) => "Fix" + enter + "  " + concrete(t, numtap + 1)
      case NLNil => ":"
      case t: NLCons => concrete(t.h) + " ~ " + concrete(t.t)
      case NLIsNil(l) => concrete(l) + "?"
      case NLHead(l) => "head(" + concrete(l) + ")"
      case NLTail(l) => "tail(" + concrete(l) + ")"
    }
  }

  @tailrec
  def full_reduce(t: NLTerm, i: Int): NLTerm = {
//    println(t)
    println(i + ": \n\t" + concrete(t))
    reduce(t) match {
      case res if res == t =>
        println("Normal Form:\n\t" + concrete(res))
        println("total step: " + i)
        res
      case res => full_reduce(res, i + 1)
    }
  }
  
  def type_check(type_env: Map[String, Type], t: Term): Type = t match {
    case UnitTerm => UnitType
    case NumV(_) => NumType
    case BoolV(_) => BoolType
    case Seq(t1, t2) => type_check(type_env, t1) match {
      case UnitType => type_check(type_env, t2)
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Var(x) => type_env(x)
    case Fun(x, xt, t) => Arrow(xt, type_check(type_env + (x -> xt), t))
    case App(f, p) => type_check(type_env, f) match {
      case Arrow(param_type, body_type) =>
        if (param_type == type_check(type_env, p)) body_type
        else throw new RuntimeException("type check fails at " + concrete(t))
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case If(c, t1, e) => type_check(type_env, c) match {
      case BoolType =>
        val t_type = type_check(type_env, t1)
        val e_type = type_check(type_env, e)
        if (t_type == e_type) t_type
        else throw new RuntimeException("type check fails at " + concrete(t))
    }
    case As(t1, ty) => if (type_check(type_env, t1) == ty) ty else throw new RuntimeException("type check fails at " + concrete(t))
    case Rec(l) => RecType(l.foldRight(List[Type]())((e, l) => type_check(type_env, e) :: l))
    case Bind(p, r, t1) =>
      type_check(type_env, r) match {
        case RecType(l) => type_check((p.l zip l).foldLeft(Map[String, Type]())((m, e) => m + (e._1->e._2)), t1)
        case _ => throw new RuntimeException("type check fails at " + concrete(t))
      }
    case Tag(_, _, ty) => ty
    case Case(t0, cm) => type_check(type_env, t0) match {
      case VarType(vm) =>
        val h = cm.head
        val ty = type_check(type_env + (h._2._1 -> vm(h._1)), h._2._2)
        if (cm.forall(e => type_check(type_env + (e._2._1 -> vm(e._1)), e._2._2) == ty)) ty else throw new RuntimeException("type check fails at " + concrete(t))
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case IsZero(t1) => type_check(type_env, t1) match {
      case NumType => BoolType
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Pred(t) => type_check(type_env, t) match {
      case NumType => NumType
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Mult(t1, t2) => (type_check(type_env, t1), type_check(type_env, t2)) match {
      case (NumType, NumType) => NumType
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Fix(t1) => type_check(type_env, t1) match {
      case Arrow(_, ty2) => ty2
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case Nil(ty) => ListType(ty)
    case Cons(ty, t1, t2) => (type_check(type_env, t1), type_check(type_env, t2)) match {
      case (ty1, ty2) if ty1 == ty && ty2 == ListType(ty)=> ListType(ty)
      case _ => throw new RuntimeException("type check fails at " + concrete(t))
    }
    case IsNil(ty, l) => if (type_check(type_env, l) == ListType(ty)) BoolType else throw new RuntimeException("type check fails at " + concrete(t))
    case Head(ty, l) => if (type_check(type_env, l) == ListType(ty)) ty else throw new RuntimeException("type check fails at " + concrete(t))
    case Tail(ty, l) => if (type_check(type_env, l) == ListType(ty)) ListType(ty) else throw new RuntimeException("type check fails at " + concrete(t))
  }

  def test(t: Term): Unit = {
    println(concrete(t))
    println("type:\n" + concrete(type_check(Map(), t)))
    val nlt = t2nl(t)
    full_reduce(nlt, 0)
  }

  val a = NLFun(NLUnitTerm)
  val b = NLFun(NLUnitTerm)
  println(a == b)

  val t1 = As(If(BoolV(true), Fun("x", BoolType, If(Var("x"), BoolV(true), BoolV(false))), Fun("y", BoolType, Var("y"))), Arrow(BoolType, BoolType))

  test(t1)

  val t2 = App(Fun("x", Arrow(BoolType, BoolType), Var("x")), Fun("x", BoolType, Var("x")))

  val t3 = Rec(List(t1, t2))

  test(t3)

  val t4 = Bind(RecPat(List("a", "b")), t3, App(Var("a"), App(Var("b"), BoolV(true))))

  test(t4)

//  VarType(m: Map[String, Type]) extends Type
  val tag = Tag("e2", Fun("notused", Arrow(UnitType, BoolType), BoolV(true)), VarType(Map("e1"->BoolType, "e2"->Arrow(Arrow(UnitType, BoolType), BoolType))))
//  case class Case(t: Term, m: Map[String, (String, Term)]) extends Term
  val case1 = ("x", If(Var("x"), BoolV(true), BoolV(false)))
  val case2 = ("y", App(Var("y"), Fun("y", UnitType, t4)))
  val t5 = Case(tag, Map("e1"->case1, "e2"->case2))

  test(t5)

  val t6 = NumV(10)

  test(t6)

  val fac = Fun("f", Arrow(NumType, NumType), Fun("n", NumType, If(IsZero(Var("n")), NumV(1), Mult(App(Var("f"), Pred(Var("n"))), Var("n")))))
  val t7 = App(Fix(fac), NumV(5))

  test(t7)

  val l = Cons(NumType, NumV(1), Cons(NumType, NumV(1), Cons(NumType, NumV(3), Nil(NumType))))
  val t8 = IsNil(NumType, l)
  test(t8)
  val t9 = IsNil(NumType, Tail(NumType, Tail(NumType, Tail(NumType, l))))
  test(t9)
  val t10 = IsNil(NumType, Tail(NumType, Tail(NumType, Tail(NumType, Tail(NumType, l)))))
  test(t10)
}
