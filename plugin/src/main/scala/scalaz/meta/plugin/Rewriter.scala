package scalaz.meta.plugin

import scala.collection.mutable
import scala.tools.nsc.Global
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.{Transform, TypingTransformers}

abstract class Rewriter extends PluginComponent with Transform with TypingTransformers { phaseFactory =>
  import Collections._

  val global: Global
  import global._
  import definitions._

  val phaseName = "rewriter"
  val runsAfter = "typer" :: Nil

  val scalazDefns: Definitions { val global: phaseFactory.global.type }
  import scalazDefns._
  lazy val ruleAnnot = rootMirror.getRequiredClass("scalaz.meta.rule")

  def newTransformer(unit: global.CompilationUnit) =
    new RewriteTransformer(unit)

  class RewriteTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree) = tree match {
      case rule@DefDef(mods, name, tparams, vparamss, tpt, ruleRhs)
          if rule.symbol.info.resultType.typeSymbol eq RewriteRuleCls =>
        val treeInfo.Applied(_, _, (lhs :: rhs :: Nil) :: Nil) = ruleRhs
        val annot = AnnotationInfo(RuleBodyAttr.tpe, lhs :: rhs :: Nil, Nil)
        rule.symbol.addAnnotation(annot)
        rule
      case Apply(fun, args) =>
        val ruleSet = rules.getOrElseUpdate(fun.symbol, {
          fun.symbol.outerClass.companionModule.toOption.toList.flatMap { companion =>
            companion.info.nonPrivateDecls.filter { mem =>
              mem.isMethod && mem.info.resultType.typeSymbol == RewriteRuleCls
            }.flatMap { mem =>
              mem.getAnnotation(RuleBodyAttr).map { rb =>
                val lhs :: rhs :: Nil = rb.args
                Rule(lhs, rhs)(mem)
              }.toList
            }
          }
        })

        ruleSet.toStream.map(_.tryMatch(tree)).find(_ ne NotMatched) match {
          case Some(mat) => mat.substed()
          case None => tree
        }
      case tree => super.transform(tree)
    }
  }

  lazy val rules: mutable.AnyRefMap[Symbol, List[Rule]] =
    perRunCaches.newAnyRefMap()

  object ListMap {
    val sym = ListClass.info.decl(nme.map)
    // a.map(b) => (a, b)
    def unapply(tree: Tree): Option[(Tree, Tree)] =  PartialFunction.condOpt(tree) {
      case treeInfo.Applied(meth @ Select(core, _), targs, (fn :: Nil) :: (cbf :: Nil) :: Nil)
          if {
            val a = (meth.symbol eq sym)
            val b = (fn.tpe.typeSymbol isNonBottomSubClass FunctionClass(1))
            //println((a, b, tree))
            a && b
          } =>
        (core, fn)
    }
  }

  final case class Rule(lhs: Tree, rhs: Tree)(sym: Symbol) {
    val tpes = sym.typeParams.toSet
    val vals = sym.paramss.head.toSet
    val descr = sym.locationString

    def tryMatch(scrut: Tree): Matched = {
      def loop(lhs: Tree, scrut: Tree): Matched = (lhs, scrut) match {
        case (emptyP, emptyS) if emptyP.isEmpty && emptyS.isEmpty => emptyMatch
        case (idP: Ident, rhs) =>
          val symP = idP.symbol
          singleMatch(symP, rhs)
        case (apP@Apply(funP, argsP), apS@Apply(funS, argsS)) =>
          val symP = apP.symbol; val symS = apS.symbol
          if ((symP eq symS) && argsP.size == argsS.size) {
            loop(funP, funS).andThen {
              argsP.zip(argsS).foldLeft(emptyMatch) { (matched, argPargS) =>
                matched andThen loop(argPargS._1, argPargS._2)
              }
            }
          } else {
            debuglog(s"Apply mismatch for $descr: $apP ($symP) / $apS (${apS.symbol})")
            NotMatched
          }
        case (selP@Select(qualP, nameP), selS@Select(qualS, nameS)) =>
          val symP = selP.symbol; val symS = selS.symbol
          if (symP eq symS) {
            if (symP.isStatic) singleMatch(symP, selS)
            else loop(qualP, qualS)
          } else {
            debuglog(s"Select mismatch for $descr: $selP ($symP) / $selS ($symS)")
            NotMatched
          }
      }

      loop(lhs, scrut) match {
        case NotMatched => NotMatched
        case m: Matched =>
          if (tpes.forall(m.tpMap.contains) && vals.forall(m.trMap.contains)) m
          else {
            debuglog(s"discarding unsaturated match: ${tpes.filterNot(m.tpMap.contains)} / ${vals.filterNot(m.trMap.contains)}")
            NotMatched
          }
      }
    }

    private def singleMatch(sym: Symbol, rhs: Tree) = {
      if (vals contains sym)
        emptyMatch withTree (sym, rhs)
      else if (tpes contains sym)
        emptyMatch withTree (sym, rhs)
      else rhs match {
        case _ if sym eq rhs.symbol => emptyMatch
        case bad =>
          debuglog(s"${rhs.shortClass} mismatch for $descr: $sym / $bad (${bad.symbol})")
          NotMatched
      }
    }

    private val emptyMatch = Matched(this, Map.empty, Map.empty)
  }
  sealed case class Matched(rule: Rule, tpMap: Map[Symbol, Type], trMap: Map[Symbol, Tree]) {
    import rule._
    def withType(param: Symbol, tp: Type): Matched = {
      assert(param.isTypeParameterOrSkolem, (rule, param, tp))
      copy(tpMap = tpMap.updated(param, tp))
    }
    def withTree(param: Symbol, tr: Tree): Matched = {
      assert(param.isValueParameter, (rule, param, tr))
      copy(trMap = trMap.updated(param, tr))
    }

    def andThen(next: => Matched) =
      if (this eq NotMatched) this else {
        val next0 = next
        if (next0 eq NotMatched) next0 else {
          assert(rule eq next0.rule, (rule, next0))
          copy(tpMap = tpMap ++ next0.tpMap, trMap = trMap ++ next0.trMap)
        }
      }

    def substed(curr: Tree = rhs): Tree = curr match {
      case _ if curr.isEmpty => curr
      case id: Ident =>
        val sym = id.symbol
        if (tpMap contains sym)
          treeCopy.TypeTree(id).setType(tpMap(sym)).setOriginal(id)
        else if (trMap contains sym) trMap(sym).duplicate
        else id
      case Apply(fun, args) =>
        treeCopy.Apply(curr, substed(fun), args map substed)
      case Select(qual, name) =>
        treeCopy.Select(curr, substed(qual), name)
      case TypeApply(qual, targs) =>
        treeCopy.TypeApply(curr, substed(qual), targs map substed)
      case other => other
    }
  }
  object NotMatched extends Matched(null, Map.empty, Map.empty) {
    override def withType(param: Symbol, tp: Type) = this
    override def withTree(param: Symbol, tp: Tree) = this
    override def toString = "NotMatched"
  }

}
