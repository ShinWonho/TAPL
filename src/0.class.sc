trait hi

case object hello extends hi

case object hihi extends hi

val a = hihi

a match {
  case hihi or hello => println("hi")
  case _ => println("hello")
}