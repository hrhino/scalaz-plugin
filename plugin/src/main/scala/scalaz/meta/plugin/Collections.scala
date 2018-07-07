package scalaz.meta.plugin

object Collections extends scala.reflect.internal.util.Collections  {

  def traverseOpt[A, B](la: List[A])(f: A => Option[B]): Option[List[B]] =
    sequence(la map f)

}
