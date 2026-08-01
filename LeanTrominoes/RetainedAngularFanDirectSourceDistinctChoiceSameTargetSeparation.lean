import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseSameTargetSeparation

/-!
# Same-target separation for distinct choices of one direct kind

The cross-clause certificates cover different local clauses of a crossover
or duplicator component.  A second finite case remains useful for the final
assembly: two different atlas incidences of the same local clause and kind.
When they converge on one variable target and their slots follow terminal
angular order, their complete Figure 7 routes are strictly separated.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- Every atlas-handled component pair of ordered, distinct choices of one
kind has a linear separator. -/
theorem
    retainedDirectSourceSameKindDistinctChoiceSameTarget_componentsLinearlySeparated :
    ∀ (kind : RetainedDirectClauseKind)
      (firstIndex secondIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstIndex.val ≠ secondIndex.val →
      let first :=
        retainedDirectSourceLocalChoice kind firstIndex
      let second :=
        retainedDirectSourceLocalChoice kind secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish →
      firstSlot.val < secondSlot.val →
      (retainedDirectSourcePrefixChoiceAt
          first.kind first.index).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          second.kind second.index).direction.angularRank →
      ∀ firstComponent secondComponent,
        retainedDirectSourceSameTargetUsesAtlasCertificate
            firstComponent secondComponent = true →
          retainedDirectSourceSameTargetComponentsLinearlySeparated
            first second firstSlot secondSlot
            firstComponent secondComponent := by
  native_decide

/-- Ordered, distinct choices of one kind converging on one target have
strictly separated complete Figure 7 routes. -/
theorem
    retainedDirectSourceSameKindDistinctChoiceSameTarget_strictlyAvoid_ordered
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (indicesDifferent : firstIndex.val ≠ secondIndex.val)
    (finishEqual :
      (retainedDirectSourceLocalChoice
        kind firstIndex).sourceSegment.finish =
      (retainedDirectSourceLocalChoice
        kind secondIndex).sourceSegment.finish)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          kind firstIndex).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          kind secondIndex).direction.angularRank) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice kind firstIndex)
        |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice kind secondIndex)
        |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice kind firstIndex
  let second :=
    retainedDirectSourceLocalChoice kind secondIndex
  have atlasCertificate :=
    retainedDirectSourceSameKindDistinctChoiceSameTarget_componentsLinearlySeparated
      kind firstIndex secondIndex firstSlot secondSlot
      indicesDifferent finishEqual slotsLt directionsLe
  have centersEqual :=
    retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
      kind kind firstIndex secondIndex finishEqual
  have componentAvoid :
      ∀ firstComponent secondComponent,
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedDirectSourceSameTargetComponentRoute
            second secondSlot secondComponent) :=
    retainedDirectSourceSameTargetComponentRoutes_strictlyAvoid
      first second firstSlot secondSlot slotsLt directionsLe
      centersEqual atlasCertificate
  have raw :=
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_components
      first second firstSlot secondSlot componentAvoid
  simpa [first, second,
    RetainedDirectSourceRouteChoice.completeFigure7Route,
    RetainedDirectSourceRouteChoice.completeRoute,
    RetainedDirectSourceRouteChoice.figure7Spoke,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourceLocalChoice] using raw

/-- Angular-order-compatible, distinct choices of one kind may be presented
in either slot order. -/
theorem
    retainedDirectSourceSameKindDistinctChoiceSameTarget_strictlyAvoid
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (indicesDifferent : firstIndex.val ≠ secondIndex.val)
    (finishEqual :
      (retainedDirectSourceLocalChoice
        kind firstIndex).sourceSegment.finish =
      (retainedDirectSourceLocalChoice
        kind secondIndex).sourceSegment.finish)
    (angularOrder :
      (retainedDirectSourceLocalChoice kind firstIndex)
        |>.AngularOrderCompatible
          (retainedDirectSourceLocalChoice kind secondIndex)
          firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice kind firstIndex)
        |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice kind secondIndex)
        |>.completeFigure7Route secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
    at angularOrder
  rcases angularOrder with
      ⟨slotsLt, directionsLe⟩ |
      ⟨slotsLt, directionsLe⟩
  · exact
      retainedDirectSourceSameKindDistinctChoiceSameTarget_strictlyAvoid_ordered
        kind firstIndex secondIndex firstSlot secondSlot
        indicesDifferent finishEqual slotsLt directionsLe
  · exact
      (retainedDirectSourceSameKindDistinctChoiceSameTarget_strictlyAvoid_ordered
        kind secondIndex firstIndex secondSlot firstSlot
        (by omega) finishEqual.symm slotsLt directionsLe).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
