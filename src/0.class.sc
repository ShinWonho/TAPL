def f1(n:Int): Unit = {
  def f2(n:Int) = {
    f1(n)
  }
  println(n)
  if (n == 1) f2(n - 1)
}

f1(1)