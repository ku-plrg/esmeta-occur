package esmeta.analyzer.tychecker

import esmeta.util.Appender.*
import esmeta.ty.*
import esmeta.util.*

/** abstract return values */
trait EffectDecl { self: TyChecker =>

  /** `invalidate` describes a call that may write any field of any object (the
    * Flow-style invalidation of every field proposition)
    */
  case class Effect(
    map: Map[String, Set[String]] = Map(),
    invalidate: Boolean = false,
  ) extends EffectLike {
    import Effect.*

    /** bottom check */
    def isBottom: Boolean = map.isEmpty && !invalidate

    /** whether a field may be written */
    def writes(field: String): Boolean =
      invalidate || map.values.exists(_.contains(field))

    /** partial order */
    def ⊑(that: Effect)(using AbsState): Boolean =
      (!this.invalidate || that.invalidate) && this.map.forall {
        case (k, v) => (that.map.contains(k) && v.subsetOf(that.map(k)))
      }

    /** not partial order */
    def !⊑(that: Effect)(using AbsState): Boolean = !(this ⊑ that)

    /** join operator */
    def ⊔(that: Effect)(using AbsState): Effect =
      Effect(
        (for {
          k <- this.map.keySet ++ that.map.keySet
        } yield k -> (this.map.getOrElse(k, Set.empty) ++ that.map
          .getOrElse(k, Set.empty))).toMap,
        this.invalidate || that.invalidate,
      )

    /** meet operator */
    def ⊓(that: Effect)(using AbsState): Effect =
      Effect(
        (for {
          k <- this.map.keySet intersect that.map.keySet
        } yield k -> (this.map.getOrElse(k, Set.empty) intersect that.map
          .getOrElse(k, Set.empty))).toMap,
        this.invalidate && that.invalidate,
      )

    def +(baseTy: String, field: Set[String]) =
      Effect(map + (baseTy -> field), invalidate)

    /** effect of writing a field of an object described by `baseTy` */
    def fieldUpdate(fld: String, baseTy: ValueTy)(using AbsState): Effect =
      this ⊔ Effect(basesOf(baseTy).map(_ -> Set(fld)).toMap)

    /** base types of an object (every base type if unknown) */
    private def basesOf(baseTy: ValueTy): Set[String] =
      baseTy.record.bases match
        case Inf      => allBases
        case Fin(set) => set.map(ManualInfo.tyModel.baseOf(_))

    def nonEmpty: Boolean = map.nonEmpty

    private def apply(rec: RecordTy): RecordTy = rec match
      case RecordTy.Top => rec
      case RecordTy.Elem(rmap) => {
        RecordTy(rmap.map((nty, fm) => {
          val base = ManualInfo.tyModel.baseOf(nty)
          val kfield =
            if (invalidate) fm.map.keySet else map.getOrElse(base, Set.empty)
          // nested records may alias the written object
          val fields = fm.kill(kfield).map.map { (field, binding) =>
            field -> binding.copy(value = apply(binding.value))
          }
          nty -> FieldMap(fields)
        }))
      }
    def apply(ty: ValueTy): ValueTy =
      if (isBottom) ty
      else
        val newList = ty.list match
          case ListTy.Elem(elem) => ListTy(apply(elem))
          case other             => other
        val newMap = ty.map match
          case MapTy.Elem(key, value) => MapTy(apply(key), apply(value))
          case other                  => other
        ty.copied(record = apply(ty.record), list = newList, map = newMap)
  }
  object Effect extends DomainLike[Effect] {

    /** top element */
    lazy val Top: Effect = exploded("Top of an Effect")

    /** bottom element */
    lazy val Bot: Effect = Effect(Map.empty)

    lazy val Empty: Effect = Effect()

    /** any field of any object may be written */
    lazy val Invalidate: Effect = Effect(invalidate = true)

    /** all base types */
    lazy val allBases: Set[String] =
      ManualInfo.tyModel.declMap.keySet.map(ManualInfo.tyModel.baseOf(_))

    /** appender */
    private given Rule[Set[String]] = iterableRule("(", ", ", ")")
    private given Rule[Map[String, Set[String]]] = sortedMapRule(sep = " -> ")
    given rule: Rule[Effect] = (app, elem) =>
      if (elem.invalidate) app >> "invalidate" else app >> elem.map
  }
}
