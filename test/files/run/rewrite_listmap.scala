import scala.tools.partest._

object Test extends DirectTest {

  def code =
    """import scalaz.meta._
      | final case class IntList(l: List[Int]) {
      |   def map(f: Int => Int): IntList = IntList(l map f)
      | }
      |
      | object IntList {
      |   val test = apply(List(1, 2, 3))
      |
      |   def mapFusion(f1: Int => Int, f2: Int => Int, l: IntList): rewrite.Rule =
      |    rewrite(l.map(f1).map(f2), l.map(f1 andThen f2))
      |}
      |object A {
      | import scalaz.meta._ ; IntList.test.map(_ + 1).map(_ - 1)
      | } """.stripMargin

  override def extraSettings =
    s"-Xprint:typer,rewriter -usejavacp -Xplugin:${sys.props("scalaz.plugin.jar")}"

  def show() = compile()

}
