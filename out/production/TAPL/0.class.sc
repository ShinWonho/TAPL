val a = Iterable(1, 2, 3, 4, 5, 2,3,4,65)
val b = Iterable(3,4,5,6,325)

def iterate(a: Iterable[Any]): Unit = a match {
  case h :: t =>
    println("h: " + h)
    println("t: " + t)
    iterate(t)
  case Nil => println("end")
  case end => println(end)
}

val m = Map(1->1, 2->3)
val keys = m.keys
val values = m.values.toList

iterate(keys zip values)


println(Nil)
println(Iterable())