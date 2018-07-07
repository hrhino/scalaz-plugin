object rules {
  import scalaz.meta._

  def listMapFusion[A, B, C](l: List[A], f1: A => B, f2: B => C): rewrite.Rule =
    rewrite(l.map(f1).map(f2), l.map(f1.andThen(f2)))
}