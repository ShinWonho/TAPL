class m_Existential_Type extends l_System_F {

  /* It extends System F with existential Type. It introduces Pack and Unpack with Existential Type. */


  /* Type */

  /* Existential Type. E stands for exist. */
  case class Ety(x: String, ty: Type) extends Type


  /* Term */

  /* Pack the Type ty and the Term t. User cannot see the ty, but alias. alias is replaced later to ty */
  case class Pack(ty: Type, t: Term, alias: Ety) extends Term

  /* Unpack the pack to X and x. X stands for the Type variable, x stands for the variable.
   * (follows the convention in TAPL.) With X and x evaluates t */
  case class Unpack(X: String, x: String, pack: Term, t: Term) extends Term


  /* extends Type Check algorithm in System F */
  override def TypeCheck(env: Env, t: Term): Type = t match {
    case Pack(ty, tPack, alias) => (TypeCheck(env, tPack), Substitution(alias.ty, tyVar(alias.x), ty)) match {
      case (expected, actual) if expected == actual => alias
      case (expected, actual) => throw new RuntimeException("Pack, expected: " + Concrete(expected) +
        " actual: " + Concrete(actual) + " in " + Concrete(t))
    }
    case Unpack(_X, x, pack, tUnpack) =>
      if (env.keys.toSet.contains(_X)) throw new RuntimeException("Unpack, " + _X + " already bounded in env to "
        + env(_X) + " in " + Concrete(t))
      TypeCheck(env, pack) match {
        case Ety(_EX, ty) =>
          if (_EX == _X) TypeCheck(env + (_X -> Dummy) + (x -> ty), tUnpack)
          else throw new RuntimeException("Ety tyVar, expected: " + _EX + " actual: " + _X + " in " + Concrete(t))
        case ty => throw new RuntimeException("Not a Pack: " + ty + " in " + Concrete(t))
      }
    case _ => super.TypeCheck(env, t)
  }


  /* extends FV in System F */
  override def FV(constraint: Set[String], fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Ety(x, ty) => FV(constraint + x, ty)

    /* Term */
    case Pack(ty, t, alias) => FV(constraint, ty) ++ FV(constraint, t) ++ FV(constraint, alias)
    case Unpack(_X, x, pack, t) => FV(constraint + _X + x, pack) ++ FV(constraint + _X + x, t)

    case fc => super.FV(constraint, fc)
  }

  /* extends BV in System F */
  override def BV(fc: FirstClass): Set[String] = fc match {
    /* Type */
    case Ety(x, ty) => BV(ty) + x

    /* Term */
    case Pack(ty, t, alias) => BV(ty) ++ BV(t) ++ BV(alias)
    case Unpack(_X, x, pack, t) => BV(pack) ++ BV(t) ++ Set(_X, x)

    case fc => super.BV(fc)
  }


  /* extends Substitution in System F */
  override def Substitution(ty: Type, from: FirstClass, to: FirstClass): Type = ty match {
    case ty if ty == from => to.asInstanceOf[Type]
    case Ety(x, ty1) => Ety(x, Substitution(ty1, from, to))
    case ty => super.Substitution(ty, from, to)
  }

  override def Substitution(t: Term, from: FirstClass, to: FirstClass): Term = t match {
    case t if t == from => to.asInstanceOf[Term]
    case Pack(ty, t, alias) =>
      Pack(Substitution(ty, from, to), Substitution(t, from, to), Substitution(alias, from, to).asInstanceOf[Ety])
    case t => super.Substitution(t, from, to)
  }


  /* extends isVal in System F */
  override def isVal(t: Term): Boolean = t match {
    case Pack(_, tPack, _) if isVal(tPack) => true
    case t => super.isVal(t)
  }


  /* extends Reduce in TypedLambda */
  override def Reduce(t: Term): Term = t match {
    case t if isVal(t) => t
    case Pack(ty, tPack, alias) => Pack(ty, Reduce(tPack), alias)
    case Unpack(_X, x, pack, tUnpack) => pack match {
      case Pack(ty, tPack, _) if isVal(tPack) =>
        Substitution(tUnpack, List(tyVar(_X), Var(x)), List(ty, tPack))
      case pack => Unpack(_X, x, Reduce(pack), tUnpack)
    }
    case t => super.Reduce(t)
  }


  /* extends Concrete in TypedLambda */
  override def Concrete(fc: FirstClass): String = fc match {
    /* Type */
    case Ety(x, ty) => "E" + x + "." + Concrete(ty)

    /* Term */
    case Pack(ty, t, alias) => "{" + Concrete(ty) + ", " + Concrete(t) + "} as " + Concrete(alias)
    case Unpack(_X, x, pack, t) => "let " + "{" + _X + ", " + x + "} = " + Concrete(pack) + " in " + Concrete(t)

    case fc => super.Concrete(fc)
  }

  println()
  println("<Existential Type>")
  println()

  /* counter ADT */
  private val counterADT =
    Pack(Num, RecT(Map("new"->NumT(1),
                       "get"->Abs("i", Num, Var("i")),
                       "inc"->Abs("i", Num, Succ(Var("i"))))),
      Ety("Counter", Rec(Map("new"->tyVar("Counter"),
                             "get"->Arrow(tyVar("Counter"), Num),
                             "inc"->Arrow(tyVar("Counter"), tyVar("Counter"))))))

  Test(counterADT)

  /* simple test */
  private val test1 =
    Unpack("Counter", "counter", counterADT,
      App(Prj(Var("counter"), "get"), App(Prj(Var("counter"), "inc"), Prj(Var("counter"), "new"))))

  Test(test1)

  /* inc 3 times */
  private val test2 =
    Unpack("Counter", "counter", counterADT,
      Let("add3", Abs("c", tyVar("Counter"),
        App(Prj(Var("counter"), "inc"), App(Prj(Var("counter"), "inc"), App(Prj(Var("counter"), "inc"), Var("c"))))),
        App(Prj(Var("counter"), "get"), App(Var("add3"), Prj(Var("counter"), "new")))))

  Test(test2)

  /* object-style ADT */

  private val counterObjectADT =
    Pack(Num, RecT(Map("state"->NumT(17),
                       "methods"->RecT(Map("get"->Abs("x", Num, Var("x")),
                                           "inc"->Abs("x", Num, Succ(Var("x"))))))),
      Ety("X", Rec(Map("state"->tyVar("X"),
                       "methods"->Rec(Map("get"->Arrow(tyVar("X"), Num),
                                          "inc"->Arrow(tyVar("X"), tyVar("X"))))))))

  Test(counterObjectADT)

  /* get method */

  private val test3 =
    Unpack("X", "body", counterObjectADT,
      App(Prj(Prj(Var("body"), "methods"), "get"), Prj(Var("body"), "state")))

  Test(test3)

  /* inc method */

  private val test4 =
    Unpack("X", "body", counterObjectADT,
      App(Prj(Prj(Var("body"), "methods"), "inc"), Prj(Var("body"), "state")))

  Test(test4)

}
