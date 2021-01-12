class l_System_F extends SimpleExtension {

  /* System F, or polymorphic lambda calculus. It introduces Type Abstraction and Type Application. */

  /* Type Environment: holds mapping and also Type Variable Binding. */


  /* Type */

  /* type variable for universal type. */
  case class tyVar(x: String) extends Type

  /* universal type. A stands for all. */
  case class Aty(x: String, ty: Type) extends Type

  /* used for debugging. It shouldn't occur in any step */
  case object Dummy extends Type


  /* Term */

  /* type abstraction */
  case class tyAbs(x: String, body: Term) extends Term

  /* type application */
  case class tyApp(ty_abs: Term, ty: Type) extends Term


  /* extends Type Check algorithm */
  override def TypeCheck(env: Env, t: Term): Type = t match {
    case tyAbs(x, body) =>
      if (env.keys.toSet.contains(x)) throw new RuntimeException("tyAbs, " + x + " already bounded in env to " +
        env(x) + " in " + Concrete(t))
      Aty(x, TypeCheck(env + (x -> Dummy), body))
    case tyApp(ty_abs, ty) => TypeCheck(env, ty_abs) match {
      case Aty(x, ty1) => Substitution(ty1, tyVar(x), ty)
      case ty1 => throw new RuntimeException("tyApp, expected: Aty actual: " + Concrete(ty1) + " in " + Concrete(t))
    }
    case t => super.TypeCheck(env, t)
  }


  /* extends FV */
  override def FV(constraint: Set[String], fc: FirstClass): Set[String] = fc match {
    /* Type */
    case tyVar(x) if constraint.contains(x).unary_! => Set(x)
    case Aty(x, ty) => FV(constraint + x, ty)

    /* Term */
    case tyAbs(x, body) => FV(constraint + x, body)
    case tyApp(ty_abs, ty) => FV(constraint, ty_abs) ++ FV(constraint, ty)

    case fc => super.FV(constraint, fc)
  }

  /* extends BV */
  override def BV(fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Aty(x, ty) => BV(ty) + x

    /* Term */
    case tyAbs(x, body) => BV(body) + x
    case tyApp(ty_abs, ty) => BV(ty_abs) ++ BV(ty)

    case fc => super.BV(fc)
  }


  /* extends Substitution */
  override def Substitution(ty: Type, from: FirstClass, to: FirstClass): Type = ty match {
    case ty if ty == from => to.asInstanceOf[Type]
    case Aty(x, ty1) => Aty(x, Substitution(ty1, from, to))
    case ty => super.Substitution(ty, from, to)
  }

  override def Substitution(t: Term, from: FirstClass, to: FirstClass): Term = t match {
    case t if t == from => to.asInstanceOf[Term]
    case tyAbs(x, body) =>
      /* note that it is impossible that any free variable in "to" includes x if it is type sound (Type checked) */
      tyAbs(x, Substitution(body, from, to))
    case tyApp(ty_abs, ty) => tyApp(Substitution(ty_abs, from, to), ty)
    case t => super.Substitution(t, from, to)
  }

  /* List of Substitution */
  def Substitution(ty: Type, from: List[FirstClass], to: List[FirstClass]): Type =
    (from zip to).foldLeft(ty)((l, e) => Substitution(l, e._1, e._2))

  def Substitution(t: Term, from: List[FirstClass], to: List[FirstClass]): Term =
    (from zip to).foldLeft(t)((l, e) => Substitution(l, e._1, e._2))


  /* extends isVal */
  override def isVal(t: Term): Boolean = t match {
    case tyAbs(_, _) => true
    case t => super.isVal(t)
  }


  /* extends Reduce */
  override def Reduce(t: Term): Term = t match {
    case t if isVal(t) => t
    case tyApp(ty_abs, ty) => ty_abs match {
      case tyAbs(x, body) => Substitution(body, tyVar(x), ty)
      case ty_abs => tyApp(Reduce(ty_abs), ty)
    }
    case t => super.Reduce(t)
  }


  /* extends Concrete */
  override def Concrete(fc: FirstClass): String = fc match {
    /* Type */
    case tyVar(x) => x
    case Aty(x, ty) => "V" + x + "." + Concrete(ty)

    /* Term */
    case tyAbs(x, body) => "{^" + x + "." + Concrete(body) + "}"
    case tyApp(ty_abs, ty) => "(" + Concrete(ty_abs) + " [" + Concrete(ty) + "]"

    case fc => super.Concrete(fc)
  }


  println()
  println("<System F>")
  println()

  /* simple test */
  private val id = tyAbs("X", Abs("x", tyVar("X"), Var("x")))
  Test(id)

  private val double = tyAbs("X", Abs("f", Arrow(tyVar("X"), tyVar("X")), Abs("a", tyVar("X"), App(Var("f"), App(Var("f"), Var("a"))))))
  Test(double)

  private val doubleNum = tyApp(double, Num)
  Test(doubleNum)

  private val doubleSucc = App(App(doubleNum, Abs("x", Num, Succ(Succ(Var("x"))))), NumT(3))
  Test(doubleSucc)


  /* List[X] */
  private val ListX = Aty("R", Arrow(Arrow(tyVar("X"), Arrow(tyVar("R"), tyVar("R"))), Arrow(tyVar("R"), tyVar("R"))))
  private val Nil = tyAbs("X",
    tyAbs("R", Abs("c", Arrow(tyVar("X"), Arrow(tyVar("R"), tyVar("R"))), Abs("n", tyVar("R"), Var("n")))))
  Test(Nil)

  private val Cons = tyAbs("X", Abs("head", tyVar("X"), Abs("tail", ListX,
    tyAbs("R", Abs("c", Arrow(tyVar("X"), Arrow(tyVar("R"), tyVar("R"))), Abs("n", tyVar("R"),
      App(App(Var("c"), Var("head")), App(App(tyApp(Var("tail"), tyVar("R")), Var("c")), Var("n")))))))))
  Test(Cons)

  private val NumNil = tyApp(Nil, Num)
  private val NumCons = tyApp(Cons, Num)

  private val NumList = App(App(NumCons, NumT(3)), App(App(NumCons, NumT(1)), App(App(NumCons, NumT(0)), NumNil)))
  Test(NumList)
}
