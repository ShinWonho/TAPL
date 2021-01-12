import scala.annotation.tailrec

object i_FJ extends App {


  /* Type of Term and Method */

  case class Class(name: String)

  case class Arrow(args: List[Class], ret: Class)


  /* Way of Declaring */

  type VarDec = Map[String, Class]

  case class MethDec(retty: Class, args: VarDec, body: Term)

  case class ClassDec(parent: String, field: VarDec, methods: Map[String, MethDec])


  /* Component of the Term */

  trait Term

  case class Var(x: String) extends Term

  case class Field(t: Term, x: String) extends Term

  case class Method(t: Term, name: String, args: List[Term]) extends Term

  case class New(name: String, args: Map[String, Term]) extends Term

  def New(name: String): New = New(name, Map())

  case class Cast(ty: Class, t: Term) extends Term


  /* Program Compile and Evaluate the CT and Term */
  class program(CT: Map[String, ClassDec], t: Term) {

    /* class and method typing */

    private def MethodTyping(name: String, method: MethDec): Boolean = {
      val retty = TypeCheck(method.args + ("this" -> Class(name)), method.body)
      if (SubType(method.retty, retty)) true
      else throw new RuntimeException("return type expected to be " + method.retty + " but " + retty + " is found")
    }

    private def ClassTyping(name: String): Boolean = CT.get(name) match {
      case Some(c) => c.methods.forall(e => MethodTyping(name, e._2))
      case None => throw new RuntimeException("no such class " + name)
    }

    CT.keys.forall(ClassTyping)


    /* helper functions for typing/evaluating rule */

    private def FieldLookup(name: String): VarDec = FieldLookup(Map(), name)

    @tailrec
    private def FieldLookup(res: VarDec, name: String): VarDec = name match {
      case "Object" => res
      case _ => CT.get(name) match {
        case Some(c) => FieldLookup(c.field ++ res, c.parent)
        case None => throw new RuntimeException("no such class " + name)
      }
    }

    @tailrec
    private def MethodTypeLookup(name: String, cname: String): Arrow = cname match {
      case "Object" => throw new RuntimeException("no such method \"" + name + "\" in " + cname)
      case _ => CT.get(cname) match {
        case Some(c) => c.methods.get(name) match {
          case Some(m) => Arrow(m.args.values.toList, m.retty)
          case None => MethodTypeLookup(name, c.parent)
        }
        case None => throw new RuntimeException("no such class " + name)
      }
    }

    @tailrec
    private def MethodBodyLookup(name: String, cname: String): (List[String], Term) = cname match {
      case "Object" => throw new RuntimeException("no such method \"" + name + "\" in " + cname)
      case _ => CT.get(cname) match {
        case Some(c) => c.methods.get(name) match {
          case Some(m) => (m.args.keys.toList, m.body)
          case None => MethodBodyLookup(name, c.parent)
        }
        case None => throw new RuntimeException("no such class " + name)
      }
    }

    /* no overloading */


    /* typing rule */

    //assume ty1 & ty2 are well typed
    @tailrec
    private def SubType(ty1: Class, ty2: Class): Boolean = (ty1, ty2) match {
      case _ if ty1 == ty2 => true
      case (Class("Object"), _) => false
      case (Class(name1), Class(name2)) => SubType(Class(CT(name1).parent), Class(name2))
    }

    private def TypeCheck(t: Term): Class = TypeCheck(Map(), t)

    private def TypeCheck(env: Map[String, Class], t: Term): Class = t match {
      case Var(x) => env.get(x) match {
        case Some(ty) => ty
        case None => throw new RuntimeException("free variable " + x)
      }
      case Field(t1, x) =>
        val c = TypeCheck(env, t1).name
        FieldLookup(c).get(x) match {
          case Some(ty) => ty
          case None => throw new RuntimeException("no matching field " + x + " to class " + c)
        }
      case Method(t1, name, args) =>
        val mtype = MethodTypeLookup(name, TypeCheck(env, t1).name)
        if ((mtype.args zip args).forall(e => SubType(TypeCheck(env, e._2), e._1))) mtype.ret
        else throw new RuntimeException("subtype failure " + mtype.args + " " + args)
      case New(name, args) => CT.get(name) match {
        case Some(c) => c.field.forall(e => args.get(e._1) match {
          case Some(t1) if SubType(TypeCheck(env, t1), e._2) => true
          case _ => throw new RuntimeException("subtype fails at" + TypeCheck(env, t1) + " " + e._2)
        })
          Class(name)
        case None => throw new RuntimeException("no such class " + name)
      }
      case Cast(cast, t) => TypeCheck(env, t) match {
        case ty if SubType(ty, cast) => cast
        case ty if SubType(cast, ty) => cast
        case ty =>
          println("Stupid from " + ty + " to " + cast)
          cast
      }
    }


    /* evaluation rule */

    private def isVal(m: Map[String, Term]): Boolean = m.values.forall(isVal)

    private def isVal(l: List[Term]): Boolean = l.forall(isVal)

    private def isVal(t: Term): Boolean = t match {
      case New(_, args) => isVal(args)
      case _ => false
    }


    private def iSubstitution(i: Iterable[Term], from: List[String], to: List[Term]): List[Term] =
      i.foldRight(List[Term]())((e, res) => Substitution(e, from, to) :: res)

    private def lSubstitution(l: List[Term], from: List[String], to: List[Term]): List[Term] = iSubstitution(l, from, to)

    private def mSubstitution(m: Map[String, Term], from: List[String], to: List[Term]): Map[String, Term] = {
      val keys = m.keys
      val values = iSubstitution(m.values, from, to)
      (keys zip values).toMap
    }

    private def Substitution(t: Term, from: List[String], to: List[Term]): Term = t match {
      case Var(x) =>
        val index = from.indexOf(x)
        if (index != -1) to(index) else Var(x)
      case Field(t0, x) => Field(Substitution(t0, from, to), x)
      case Method(t0, name, args) => Method(Substitution(t0, from, to), name, lSubstitution(args, from, to))
      case New(name, args) => New(name, mSubstitution(args, from, to))
      case Cast(ty, t0) => Cast(ty, Substitution(t0, from, to))
    }


    private def iReduce(i: Iterable[Term]): List[Term] = iReduce(i, List())

    @tailrec
    private def iReduce(l: Iterable[Term], res: List[Term]): List[Term] = l match {
      case h :: t => h match {
        case v if isVal(v) => iReduce(t, res :+ v)
        case _ => res ::: Reduce(h) :: t
      }
      case Nil =>
        println("ERROR: All values already!")
        res
    }

    private def lReduce(l: List[Term]): List[Term] = iReduce(l)

    private def mReduce(m: Map[String, Term]): Map[String, Term] = {
      val keys = m.keys
      val values = iReduce(m.values.toList)
      (keys zip values).toMap
    }

    private def Reduce(t: Term): Term = t match {
      case Field(t1, x) => t1 match {
        case New(_, args) if isVal(t1) => args(x)
        case _ => Field(Reduce(t1), x)
      }
      case Method(t1, name, args) => t1 match {
        case New(cname, _) if isVal(t1) && isVal(args) =>
          val mbody = MethodBodyLookup(name, cname)
          val from = "this" :: mbody._1
          val to = t1 :: args
          Substitution(mbody._2, from, to)
        case _ if isVal(t1) => Method(t1, name, lReduce(args))
        case _ => Method(Reduce(t1), name, args)
      }
      case New(name, args) => args match {
        case _ if isVal(args) => New(name, args)
        case _ => New(name, mReduce(args))
      }
      case Cast(ty, t1) => t1 match {
        case _ if isVal(t1) => t1
        case _ => Cast(ty, Reduce(t1))
      }
    }


    private def iConcrete(i: Iterable[Term]): List[String] = i.foldRight(List[String]())((e, l) => Concrete(e) :: l)

    private def lConcrete(l: List[Term]): String = lConcrete(iConcrete(l), "")

    @tailrec
    private def lConcrete(l: List[String], res: String): String = l match {
      case h :: t if t == Nil => res + h
      case h :: t => lConcrete(t, res + h + ", ")
      case Nil => res
    }

    private def mConcrete(m: Map[String, Term]): String = {
      val keys = m.keys.toList
      val values = iConcrete(m.values)
      mConcrete(keys zip values, "")
    }

    @tailrec
    private def mConcrete(l: List[(String, String)], res: String): String = l match {
      case h :: t if t == Nil => res + h._1 + " = " + h._2
      case h :: t => mConcrete(t, res + h._1 + " = " + h._2 + ", ")
      case Nil => res
    }

    private def Concrete(t: Term): String = t match {
      case Var(x) => x
      case Field(t0, x) => Concrete(t0) + "." + x
      case Method(t0, name, args) => Concrete(t0) + "." + name + "(" + lConcrete(args) + ")"
      case New(name, args) => "new " + name + "(" + mConcrete(args) + ")"
      case Cast(ty, t0) => "((" + ty.name + ")@" + Concrete(t0) + ")"
    }


    private def FullReduce(t: Term): Term = FullReduce(t, 0)

    @tailrec
    private def FullReduce(t: Term, i: Int): Term = {
      println("\t" + i + ": " + Concrete(t))
      Reduce(t) match {
        case res if res == t => res
        case res => FullReduce(res, i + 1)
      }
    }


    private def Test(t: Term): Unit = {
      println(Concrete(t))
      println(TypeCheck(t))
      FullReduce(t)
      println()
    }

    Test(t)
  }


  /* Class Table */

  val ct: Map[String, ClassDec] = Map(
    "A" -> ClassDec(
      parent = "Object",
      field = Map(),
      //        constr = Constructor(List()),
      methods = Map()
    ),
    "B" -> ClassDec(
      parent = "Object",
      field = Map(),
      methods = Map()
    ),
    "Pair" -> ClassDec(
      parent = "Object",
      field = Map(
        "first" -> Class("Object"),
        "second" -> Class("Object")),
      methods = Map(
        "setfirst" -> MethDec(Class("Pair"), Map(("newfirst", Class("Object"))),
          New("Pair", Map("first" -> Var("newfirst"), "second" -> Field(Var("this"), "second"))))
      )
    )
  )


  val t1 =
    Method(
      New("Pair", Map(
        "first" -> New("A"),
        "second" -> New("B"))),
      "setfirst", List(New("B")))

  new program(ct, t1)

  val t2 =
    Field(Cast(Class("Pair"), Field(
      New("Pair", Map(
        "first" ->
          New("Pair", Map(
            "first" -> New("A"),
            "second" -> New("B"))),
        "second" -> New("A"))),
      "first")), "second")

  new program(ct, t2)
}
