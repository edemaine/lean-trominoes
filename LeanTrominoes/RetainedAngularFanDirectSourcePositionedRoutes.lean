import LeanTrominoes.RetainedAngularFanDirectSourceTailSeparation

/-!
# Positioned coordinated routes for direct source clauses

The direct-source atlas is expressed in each component's local coordinates.
In the final construction the local component is first translated by its
macrocell origin, then scaled by the source-clearance factor four, and
finally refined by the complete fan factor.

This file names that combined translation and transports the certified
coordinated complete routes into physical coordinates.  Pairwise avoidance
and common-head-only contact are invariant under this common translation,
so later metadata integration needs only identify the component origin and
the two atlas entries.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Physical translation induced by first translating a direct template,
then source-scaling by four, and finally applying the fan refinement. -/
def retainedDirectSourceFanPositioningOffset
    (origin : Cell) : Cell :=
  Cell.scale retainedTerminalFanTotalRefinement
    (Cell.scale 4 origin)

/-- The concrete factor-four fan center placed at a direct component
origin. -/
def retainedDirectSourcePositionedFanCenterAt
    (origin : Cell)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    Cell :=
  Cell.add
    (retainedDirectSourceFanPositioningOffset origin)
    (retainedDirectSourceFanCenterAt kind index)

/-- A coordinated complete direct-source route translated into its physical
component coordinates. -/
def retainedDirectSourcePositionedFanCompleteRouteAt
    (origin : Cell)
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    List Cell :=
  translatePolyline
    (retainedDirectSourceFanPositioningOffset origin)
    (retainedDirectSourceFanCompleteRouteAt
      kind index slot)

/-- Positioning a metadata-selected direct literal pair preserves both
continuous avoidance and the fact that its shared clause gate is the only
possible contact. -/
theorem
    RetainedDirectSourcePrefixPairSelection.positionedCompleteRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : PeriodicOrthocrossing.DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (origin : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesAvoidEachOther
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.secondIndex secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.firstIndex firstSlot)
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.secondIndex secondSlot) := by
  have separated := selection.completeRoutes_separated
    firstSlot secondSlot
  exact
    ⟨separated.1.translate
        (retainedDirectSourceFanPositioningOffset origin),
      separated.2.translate
        (retainedDirectSourceFanPositioningOffset origin)⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
