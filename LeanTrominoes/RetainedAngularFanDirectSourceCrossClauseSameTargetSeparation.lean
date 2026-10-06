/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates

/-!
# Cross-clause direct routes at one target center

Two incidences from different local clauses can converge on the same
variable center.  Their occurrence slots are not arbitrary: the angular
occurrence order assigns increasing slots to nondecreasing retained terminal
directions.  This file isolates that order-compatible local geometry for the
crossover and duplicator atlases.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every atlas-handled component pair of an ordered same-target crossover
pair has a linear separator. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_componentsLinearlySeparated :
    ∀ (firstClauseIndex secondClauseIndex : Fin 26)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstClauseIndex ≠ secondClauseIndex →
      let first :=
        retainedDirectSourceLocalChoice
          (.crossover firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex
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
  intro firstClause secondClause firstIndex secondIndex firstSlot secondSlot different
  dsimp only
  intro sameTarget slotsOrdered ranksOrdered firstComponent secondComponent used
  have checked := crossoverSameTargetCheck_correct firstClause
  simp only [crossoverSameTargetCheck, sameTargetLocalChoicesCheck, finiteAll_eq_true,
    guardedCheck_eq_true] at checked
  exact sameTargetPiecesCheck_sound _ _ firstSlot secondSlot firstComponent secondComponent
    (checked secondClause different firstIndex secondIndex sameTarget ranksOrdered
      firstSlot secondSlot slotsOrdered firstComponent secondComponent used)

/-- Every atlas-handled component pair of an ordered same-target duplicator
pair has a linear separator. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_componentsLinearlySeparated :
    ∀ (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
      (firstClauseIndex secondClauseIndex : Fin 2)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator firstArm firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator secondArm secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      (firstArm, firstClauseIndex) ≠
          (secondArm, secondClauseIndex) →
      let first :=
        retainedDirectSourceLocalChoice
          (.duplicator firstArm firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex) secondIndex
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
  intro firstArm secondArm firstClause secondClause firstIndex secondIndex firstSlot secondSlot different
  dsimp only
  intro sameTarget slotsOrdered ranksOrdered firstComponent secondComponent used
  have checked := duplicatorSameTargetCheck_correct firstArm firstClause
  simp only [duplicatorSameTargetCheck, sameTargetLocalChoicesCheck, finiteAll_eq_true,
    guardedCheck_eq_true] at checked
  exact sameTargetPiecesCheck_sound _ _ firstSlot secondSlot firstComponent secondComponent
    (checked secondArm secondClause different firstIndex secondIndex sameTarget ranksOrdered
      firstSlot secondSlot slotsOrdered firstComponent secondComponent used)

/-- Ordered different crossover clauses converging on one target have
strictly separated complete Figure 7 routes. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
    (firstClauseIndex secondClauseIndex : Fin 26)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent : firstClauseIndex ≠ secondClauseIndex)
    (finishEqual :
      let first :=
        retainedDirectSourceLocalChoice
          (.crossover firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          (.crossover firstClauseIndex) firstIndex).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          (.crossover secondClauseIndex) secondIndex).direction.angularRank) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.crossover firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.crossover secondClauseIndex) secondIndex
  have atlasCertificate :=
    retainedDirectSourceCrossoverCrossClauseSameTarget_componentsLinearlySeparated
      firstClauseIndex secondClauseIndex firstIndex secondIndex
      firstSlot secondSlot clausesDifferent finishEqual
      slotsLt directionsLe
  have centersEqual :=
    retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
      (.crossover firstClauseIndex)
      (.crossover secondClauseIndex)
      firstIndex secondIndex finishEqual
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

/-- Ordered different duplicator clauses converging on one target have
strictly separated complete Figure 7 routes. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
    (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
    (firstClauseIndex secondClauseIndex : Fin 2)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator firstArm firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator secondArm secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent :
      (firstArm, firstClauseIndex) ≠
        (secondArm, secondClauseIndex))
    (finishEqual :
      let first :=
        retainedDirectSourceLocalChoice
          (.duplicator firstArm firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          (.duplicator firstArm firstClauseIndex)
          firstIndex).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          (.duplicator secondArm secondClauseIndex)
          secondIndex).direction.angularRank) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.duplicator firstArm firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.duplicator secondArm secondClauseIndex) secondIndex
  have atlasCertificate :=
    retainedDirectSourceDuplicatorCrossClauseSameTarget_componentsLinearlySeparated
      firstArm secondArm firstClauseIndex secondClauseIndex
      firstIndex secondIndex firstSlot secondSlot
      clausesDifferent finishEqual slotsLt directionsLe
  have centersEqual :=
    retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
      (.duplicator firstArm firstClauseIndex)
      (.duplicator secondArm secondClauseIndex)
      firstIndex secondIndex finishEqual
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

/-- Angular-order-compatible crossover routes from different clauses may be
presented in either slot order. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid
    (firstClauseIndex secondClauseIndex : Fin 26)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent : firstClauseIndex ≠ secondClauseIndex)
    (finishEqual :
      (retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex).sourceSegment.finish =
        (retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex).sourceSegment.finish)
    (angularOrder :
      (retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.AngularOrderCompatible
            (retainedDirectSourceLocalChoice
              (.crossover secondClauseIndex) secondIndex)
            firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
    at angularOrder
  rcases angularOrder with
      ⟨slotsLt, directionsLe⟩ |
      ⟨slotsLt, directionsLe⟩
  · exact
      retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
        firstClauseIndex secondClauseIndex firstIndex secondIndex
        firstSlot secondSlot clausesDifferent finishEqual
        slotsLt directionsLe
  · exact
      (retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
        secondClauseIndex firstClauseIndex secondIndex firstIndex
        secondSlot firstSlot clausesDifferent.symm finishEqual.symm
        slotsLt directionsLe).symm

/-- Angular-order-compatible duplicator routes from different local clauses
may be presented in either slot order. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid
    (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
    (firstClauseIndex secondClauseIndex : Fin 2)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator firstArm firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator secondArm secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent :
      (firstArm, firstClauseIndex) ≠
        (secondArm, secondClauseIndex))
    (finishEqual :
      (retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex)
          firstIndex).sourceSegment.finish =
        (retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex)
          secondIndex).sourceSegment.finish)
    (angularOrder :
      (retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.AngularOrderCompatible
            (retainedDirectSourceLocalChoice
              (.duplicator secondArm secondClauseIndex) secondIndex)
            firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
    at angularOrder
  rcases angularOrder with
      ⟨slotsLt, directionsLe⟩ |
      ⟨slotsLt, directionsLe⟩
  · exact
      retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
        firstArm secondArm firstClauseIndex secondClauseIndex
        firstIndex secondIndex firstSlot secondSlot
        clausesDifferent finishEqual slotsLt directionsLe
  · exact
      (retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
        secondArm firstArm secondClauseIndex firstClauseIndex
        secondIndex firstIndex secondSlot firstSlot
        clausesDifferent.symm finishEqual.symm
        slotsLt directionsLe).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
