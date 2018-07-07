package scalaz.meta

import com.github.ghik.silencer.silent
import scala.Any
import scala.annotation.StaticAnnotation

trait Typeclass

class orphan extends StaticAnnotation

@silent
class minimal(defns: Any*) extends StaticAnnotation

object features {
  @scala.annotation.meta.languageFeature("enable orphan instances", enableRequired = true)
  sealed trait orphans
  object orphans extends orphans
}

object enable {
  implicit lazy val orphans: features.orphans = features.orphans
}

object rewrite {
  type Rule

  @silent def apply[T](from: T, to: T): Rule = scala.sys.error("rewrite")

  @silent
  private[scalaz] final class ruleBody(body: Any) extends StaticAnnotation
}


