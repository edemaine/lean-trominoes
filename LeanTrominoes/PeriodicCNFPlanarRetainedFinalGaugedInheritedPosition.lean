/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-! # Exact inherited positions after clearance, Figure 9, and final gauging -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Inherited variables are scaled by clearance two, Figure 9 twelve, and
unit elimination six. Their natural positions already lie inside the final
period, so quotient gauging leaves those positions unchanged. -/
theorem retainedFinalGaugedInheritedPosition
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable))
    (member : atom ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).erase.variableOccurrences) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source).position
      (.inl (.inl atom)) =
      Cell.scale 144 ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position atom) := by
  let placement := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let raw := retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement source
  have rawPosition : raw.position (.inl (.inl atom)) = Cell.scale 144 (placement.position atom) := by
    apply Prod.ext <;>
      simp [raw, placement, retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
        PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
        PeriodicOneInThreeNoUnitsPositioned.placement, PeriodicOneInThreePositioned.placement,
        retainedFigureNineClearancePlacement, PeriodicVariablePlacement.scale_position,
        retainedFigureNineSourceClearanceFactor, PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale, Cell.scale] <;> ring
  have rawPeriod : raw.period = 144 * placement.period := by
    simp [raw, placement, retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement, PeriodicOneInThreePositioned.placement,
      retainedFigureNineClearancePlacement, PeriodicVariablePlacement.scale_period,
      retainedFigureNineSourceClearanceFactor, PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
    omega
  have inside := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_inSquare_of_mem
    source atom member
  change 0 < (placement.position atom).1 ∧ (placement.position atom).1 < placement.period ∧
    0 < (placement.position atom).2 ∧ (placement.position atom).2 < placement.period at inside
  change (raw.variableGauge raw.canonicalPositionGauge).position (.inl (.inl atom)) = _
  rw [PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position, rawPosition, rawPeriod]
  simp only [Cell.scale, Nat.cast_mul, Nat.cast_ofNat]
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]

end LeanTrominoes.PeriodicOrthocrossing
