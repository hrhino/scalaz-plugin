package scalaz
package plugin

import scala.tools.nsc._
import scala.reflect.internal.Flags
import scala.tools.nsc.transform.InfoTransform

/** Converts `@adt` definitions to more ADT-like representations.
  *
  *
  */
trait ADTs extends plugins.PluginComponent with InfoTransform with Utils {

  val global: Global
  val scalazDefns: Definitions { val global: ADTs.this.global.type }
  import global._, definitions._, scalazDefns._, Flags._

  override val phaseName  = "adt"
  override val runsAfter  = "typer"   :: Nil
  override val runsBefore = "pickler" :: Nil

  object ADTAnalyzer extends analyzer.AnalyzerPlugin with analyzer.MacroPlugin {
    import analyzer.{global => _, _}

    // the scaladoc says this is the right impl; I'll leave it like this until
    // someone finds a bug, I guess
    override def isActive() = global.phase.id < global.currentRun.picklerPhase.id

    override def pluginsTypeSig(tpe: Type, typer: Typer, defTree: Tree, pt: Type): Type = {
      import typer.{context, namer}
      val sym = context.owner // the symbol that will be given to defTree
      defTree match {
        case cd: ClassDef if isAdt(sym) =>
          if (sym.hasFlag(FINAL))
            globalError(cd.pos, "@data classes may not be final")
          if (sym.hasFlag(CASE))
            globalError(cd.pos, "@data classes may not be case")
          // @data classes are implicitly sealed abstract
          sym.setFlag(SEALED | ABSTRACT)
          modifyParents(tpe) { parents =>
            val newParents = List(ProductRootClass.tpe, SerializableTpe)
              .filterNot(parents.contains)
            parents ::: newParents
          }
          currentUnit.synthetics
        case cd: ClassDef if isAdtCase(sym) =>
          val adt = sym.owner.companionClass
          // now we have a (for now, case) class inside of a companion module of
          // a @data class. I want to remove the `case`ness and have it be
          // written as a normal class with case semantics, but that requires
          // extra work. for now, they _must_ be case (but we're gonna be rude
          // and override the apply method anyways, because that's the entire
          // point of this exercise, isn't it?
          if (!sym.isCase) {

          }
          modifyParents(tpe) { parents =>
            if (tpe.baseClasses contains adt) parents
            else if (adt.isTrait) parents.head :: adt.tpe_* :: parents.tail
            else adt.tpe_* :: parents.tail
          }
        case apply@DefDef(_, nme.apply, _, _, _, _) if isAdtModule(sym.owner.owner) =>
          def modifyRestpe(tp: Type): Type = tp match {
            case PolyType(tparams, restpe)   =>
              PolyType(tparams, modifyRestpe(restpe))
            case MethodType(vparams, restpe) =>
              MethodType(vparams, modifyRestpe(restpe))
            case restpe                      =>
              val newRestpe = sym.owner.owner.companionClass.tpe_*
              assert(restpe <:< newRestpe, (restpe, newRestpe))
              newRestpe
          }
          sym.updateAttachment(ADTCaseConstructorOriginalType(tpe))
          modifyRestpe(tpe)
        case _ =>
          tpe
      }
    }
  }

  /** Stores the original tpe of the `apply` method of a case constructor of
    * an ADT. This allows the compiler rewrite of
    *
    * @param tpe
    */
  case class ADTCaseConstructorOriginalType(tpe: Type)

  def newTransformer(unit: CompilationUnit) = new Transformer {
    override def transform(tree: Tree) = tree match {
      case tree: SymTree if tree.symbol.hasAttachment[ADTCaseConstructorOriginalType] =>
        tree.setType(exitingPhase(currentRun.phaseNamed("adt"))(tree.symbol.info))
      case _ => super.transform(tree)
    }
  }
  def transformInfo(sym: Symbol, tpe: Type): Type =
    sym.attachments.get[ADTCaseConstructorOriginalType] match {
      case Some(ADTCaseConstructorOriginalType(origTpe)) =>
        origTpe
      case _                                             => tpe
    }

  /* The actual requirements are stricter, but we check them on the annotated
     * tree, given that the annotation is present and that it's a class. */
  def isAdt(sym: Symbol): Boolean =
    sym.isClass && sym.hasAnnotation(AdtAttr)

  def isAdtModule(sym: Symbol): Boolean =
    sym.isModuleOrModuleClass && sym.companionClass.exists && isAdt(sym.companionClass)

  def isAdtCase(sym: Symbol): Boolean =
     sym.owner.isModuleClass && isAdt(sym.owner.companionClass)

  final def register(): Unit = {
    analyzer.addAnalyzerPlugin(ADTAnalyzer)
    analyzer.addMacroPlugin(ADTAnalyzer)
  }
}

