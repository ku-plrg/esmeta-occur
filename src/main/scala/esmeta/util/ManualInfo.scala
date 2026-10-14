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

  /** patches of the type model for the target version, set by the extractor
    * before the type model is used. Each file `<n>-<commit>.diff` in
    * `types-patch` is a unified diff of `types` for the commit and its
    * descendants, applied in the order of <n>.
    */
  var tyModelPatches: List[String] = Nil

  /** type model */
  lazy val tyModel: TyModel =
    val base = s"$MANUALS_DIR/types"
    if (tyModelPatches.isEmpty) TyModel.fromFile(base)
    else
      val file = java.io.File.createTempFile("types", "")
      file.deleteOnExit
      executeCmd(s"cp $base $file")
      for (patch <- tyModelPatches) executeCmd(s"patch -s $file $patch")
      TyModel.fromFile(file.toString)

  /** choose the type model patches for a version */
  def selectTyModel(isDescendant: String => Boolean): Unit =
    val pattern = "([0-9]+)-([0-9a-f]+)\\.diff".r
    tyModelPatches = (for {
      file <- getFiles(_.endsWith(".diff"))
      if file.getParentFile.getName == "types-patch"
      (n, commit) <- file.getName match
        case pattern(n, commit) => Some((n.toInt, commit))
        case _                  => None
      if isDescendant(commit)
    } yield n -> file.toString).sortBy(_._1).map(_._2)

  /** find all files in the manual directory with a filter */
  private def getFiles(filter: String => Boolean): List[File] = (for {
    file <- walkTree(MANUALS_DIR)
    if filter(file.getName)
  } yield file).toList

  /** find all file names in the manual directory with a filter */
  private def getFileNames(filter: String => Boolean): List[String] =
    getFiles(filter).map(_.toString)
}
