package esmeta.util

import esmeta.MANUALS_DIR
import esmeta.analyzer.tychecker.TyChecker.Ignore
import esmeta.spec.Spec
import esmeta.ty.TyModel
import esmeta.util.BaseUtils.*
import esmeta.util.SystemUtils.*
import java.io.File

/** manual information helpers */
object ManualInfo {

  /** A list of algorithms to ignore for tycheck */
  lazy val tycheckIgnore: Ignore = Ignore(s"$MANUALS_DIR/tycheck-ignore.json")

  /** manual algorithm files */
  lazy val algoFiles: List[String] = getFileNames(algoFilter)

  /** manual IR function files */
  lazy val funcFiles: List[String] = getFileNames(irFilter)

  /** manual compilation rule */
  lazy val compileRule: CompileRule =
    readJson[CompileRule](s"$MANUALS_DIR/rule.json")
  type CompileRule = Map[String, Map[String, String]]

  /** bugfix patch map */
  lazy val bugfixPatchMap: Map[String, String] = (for {
    file <- getFiles(patchFilter)
    name = file.getName
    pattern = "(.*).patch".r
    hash <- name match
      case pattern(hash) => Some(hash)
      case _             => None
  } yield hash -> file.toString).toMap

  /** type model */
  lazy val tyModel: TyModel =
    import esmeta.ty.util.JsonProtocol.given
    TyModel.fromFile(s"$MANUALS_DIR/types")

  /** find all files in the manual directory with a filter */
  private def getFiles(filter: String => Boolean): List[File] = (for {
    file <- walkTree(MANUALS_DIR)
    if filter(file.getName)
  } yield file).toList

  /** find all file names in the manual directory with a filter */
  private def getFileNames(filter: String => Boolean): List[String] =
    getFiles(filter).map(_.toString)
}
