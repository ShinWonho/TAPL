class TypedLambda {

  /* Typed Lambda Calculus with only Variable, Abstraction, and Application.
   * It reduces the App in call-by-value order.
   * To extend the system, Type Check, FV/BV, Substitution, isVal, Reduce, Concrete should be extended. */

  import scala.annotation.tailrec

  import scala.util.Random


  /* limit of the length of the variable name. # of available variable name is 62^NAMELENGTH.
   * But it should be guaranteed that (# of variable names used in context) << (62^NAMELENGTH) for efficiency */
  val NAMELENGTH = 1

  /* Type Environment: mapping from string to Type */
  type Env = Map[String, Type]


  /* both Type and Term are first class */
  trait FirstClass


  /* Type */
  trait Type extends FirstClass

  /* abstraction type */
  case class Arrow(paramTy: Type, bodyTy: Type) extends Type


  /* Term */
  trait Term extends FirstClass

  /* variable */
  case class Var(x: String) extends Term

  /* abstraction */
  case class Abs(x: String, ty: Type, body: Term) extends Term

  /* application */
  case class App(abs: Term, param: Term) extends Term


  /* Checks the Type safety of the Term t. If Type Check fails, throw exception, else return the Type of t */
  def TypeCheck(t: Term): Type = TypeCheck(Map(), t)

  def TypeCheck(env: Env, t: Term): Type = t match {
    case Var(x) => env.get(x) match {
      case Some(ty) => ty
      case None => throw new RuntimeException("Free Variable " + x)
    }
    case Abs(x, ty, body) => Arrow(ty, TypeCheck(env + (x -> ty), body))
    case App(abs, param) => TypeCheck(env, abs) match {
      case Arrow(paramTy, bodyTy) => (TypeCheck(env, param), paramTy) match {
        case (expected, actual) if expected == actual => bodyTy
        case (expected, actual) => throw new RuntimeException("App, expected: " + Concrete(expected) +
          " actual: " + Concrete(actual) + " in " + Concrete(t))
      }
      case ty => throw new RuntimeException("Not an Abs: " + Concrete(ty) + " in " + Concrete(t))
    }
  }


  /* It introduces new name with constraints */
  @tailrec
  final def IntroduceName(constraint: Set[String]): String = {
    //    println("Introduce name with constraint " + constraint)
    val new_name = "a" + Random.alphanumeric.take(NAMELENGTH).mkString
    if (constraint contains new_name) IntroduceName(constraint) else new_name
  }


  /* It guarantees capture free Substitution */
  def AlphaConversion(constraint: Set[String], t: Abs): Abs = {
    val free_variables = FV(t.body)
    val bound_variables = BV(t.body)
    val new_name = IntroduceName(constraint ++ free_variables ++ bound_variables)
    Abs(new_name, t.ty, Substitution(t.body, Var(t.x), Var(new_name)))
  }


  /* It finds free variables in the Type ty or the Term t. */
  def FV(fc: FirstClass): Set[String] = FV(Set(), fc)

  /* It checks whether the variable is free or not using constraint. Bound variable is the Set constraint.
   * So if the variable is not in the constraint, it is free. */
  def FV(constraint: Set[String], fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Arrow(paramTy, bodyTy) => FV(constraint, paramTy) ++ FV(constraint, bodyTy)

    /* Term */
    case Var(x) if constraint.contains(x).unary_! => Set(x)
    case Abs(x, _, body) => FV(constraint + x, body)
    case App(abs, param) => FV(constraint, abs) ++ FV(constraint, param)
    case _ => Set()
  }

  /* It finds bound variables in the Type ty or the Term t */
  def BV(fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Arrow(paramTy, bodyTy) => BV(paramTy) ++ BV(bodyTy)

    /* Term */
    case Abs(x, _, body) => BV(body) + x
    case App(abs, param) => BV(abs) ++ BV(param)
    case _ => Set()
  }


  /* Substitute every occurrence "from" to "to" in the Type ty or the Term t. */
  def Substitution(ty: Type, from: FirstClass, to: FirstClass): Type = ty match {
    case ty if ty == from => to.asInstanceOf[Type]
    case Arrow(paramTy, bodyTy) => Arrow(Substitution(paramTy, from, to), Substitution(bodyTy, from, to))
    case ty => ty
  }

  def Substitution(t: Term, from: FirstClass, to: FirstClass): Term = t match {
    case t if t == from => to.asInstanceOf[Term]
    case Abs(x, ty, body) =>
      if (from == Var(x)) Abs(x, ty, body)
      else {
        /* It assures "capture free" */
        val free_variables = FV(to)
        val t = if (free_variables.contains(x)) AlphaConversion(free_variables, Abs(x, ty, body)) else Abs(x, ty, body)
        Abs(t.x, t.ty, Substitution(t.body, from, to))
      }
    case App(abs, param) => App(Substitution(abs, from, to), Substitution(param, from, to))
    case t => t
  }


  /* Check whether the term is a value or not */
  def isVal(t: Term): Boolean = t match {
    case Abs(_, _, _) => true
    case _ => false
  }


  /* Reduce the Term t */
  def Reduce(t: Term): Term = t match {
    case t if isVal(t) => t
    case App(abs, param) => abs match {
      case Abs(x, _, body) =>
        if (isVal(param)) Substitution(body, Var(x), param)
        else App(abs, Reduce(param))
      case abs => App(Reduce(abs), param)
    }
    case t => t
  }


  /* Term and Type into readable String */
  def Concrete(fc: FirstClass): String = fc match {
    /* Type */
    case Arrow(paramTy, bodyTy) => "(" + Concrete(paramTy) + "->" + Concrete(bodyTy) + ")"

    /* Term */
    case Var(x) => x
    case Abs(x, _, body) => "{^" + x + "." + Concrete(body) + "}"
    case App(abs, param) => "(" + Concrete(abs) + " " + Concrete(param) + ")"
  }


  /* Keep reducing the Term until it become the normal form. Also it prints each step */
  def FullReduce(t: Term): Term = FullReduce(t, 0)

  @tailrec
  private def FullReduce(t: Term, i: Int): Term = {
    /* show step for debugging */
//    println("\t" + i + ": " + Concrete(t))
    Reduce(t) match {
      case res if res == t => res
      case res => FullReduce(res, i + 1)
    }
  }


  /* Test the Term. It prints, Type Check t, and Full Reduce the Term t */
  def Test(t: Term): Unit = {
    println("Term: " + Concrete(t))
    println("Type: " + Concrete(TypeCheck(t)))
    println("Norm: " + Concrete(FullReduce(t)))
    println()
  }


}
