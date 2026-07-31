import LeanTrominoes.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-!
# Direct-source prefixes versus Figure 7 spokes

The coordinated direct-source atlas routes each literal from its common
clause gate to the boundary of its selected occurrence macrocell.  This
module places the actual factor-eight Figure 7 spoke at that same local
center and exhaustively certifies both directed cross interactions for
every pair of different atlas entries and every pair of occurrence slots.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The factor-eight Figure 7 spoke centered at the local endpoint of one
direct-source atlas entry. -/
def retainedDirectSourceFigure7SpokeAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : List Cell :=
  translatePolyline
    (Cell.sub
      (retainedDirectSourceFanCenterAt kind index)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline retainedTerminalFanRoutingRefinement
      (spokeRoute (angularPortOfIndex slot.val)))

/-- Both directed prefix--spoke interactions are contact-free for every
pair of different entries in one direct-clause atlas. -/
def RetainedDirectClauseKind.SourceFigure7SpokesCrossSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length),
    firstIndex ≠ secondIndex →
    ∀ firstSlot secondSlot : RetainedTerminalSlot,
      RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFanCompleteRouteAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFigure7SpokeAt
            kind secondIndex secondSlot) ∧
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFigure7SpokeAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFanCompleteRouteAt
            kind secondIndex secondSlot)

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceFigure7SpokesCrossSeparated := by
  unfold
    RetainedDirectClauseKind.SourceFigure7SpokesCrossSeparated
  let firstDecidable :
      ∀ firstIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            firstIndex ≠ secondIndex →
            ∀ firstSlot secondSlot : RetainedTerminalSlot,
              RoutesStrictlyAvoidEachOther
                  (retainedDirectSourceFanCompleteRouteAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFigure7SpokeAt
                    kind secondIndex secondSlot) ∧
                RoutesStrictlyAvoidEachOther
                  (retainedDirectSourceFigure7SpokeAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFanCompleteRouteAt
                    kind secondIndex secondSlot)) :=
    fun firstIndex => by
      letI :
          ∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            Decidable
              (firstIndex ≠ secondIndex →
              ∀ firstSlot secondSlot : RetainedTerminalSlot,
                RoutesStrictlyAvoidEachOther
                    (retainedDirectSourceFanCompleteRouteAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFigure7SpokeAt
                      kind secondIndex secondSlot) ∧
                  RoutesStrictlyAvoidEachOther
                    (retainedDirectSourceFigure7SpokeAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFanCompleteRouteAt
                      kind secondIndex secondSlot)) :=
        fun _ => inferInstance
      exact Fintype.decidableForallFintype
  letI := firstDecidable
  exact Fintype.decidableForallFintype

/-- Exhaustive finite certificate for the direct-source/Figure 7 cross
interactions. -/
theorem retainedDirectSourceFigure7SpokesCrossSeparated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceFigure7SpokesCrossSeparated := by
  native_decide

/-- Public pointwise form of the exhaustive cross-separation certificate. -/
theorem retainedDirectSourceFanCompleteRoutes_crossSpokes_strictlyAvoid
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFigure7SpokeAt
          kind secondIndex secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFigure7SpokeAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          kind secondIndex secondSlot) :=
  retainedDirectSourceFigure7SpokesCrossSeparated
    kind firstIndex secondIndex indicesDifferent
      firstSlot secondSlot

end PeriodicEightOccurrenceSplit
end LeanTrominoes
