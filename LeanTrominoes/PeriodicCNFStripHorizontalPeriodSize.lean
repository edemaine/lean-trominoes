/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripSourceFormulaSize

/-!
# Physical period of the horizontal retained construction
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The only input-dependent geometric scale before the retained fixed
refinements are applied. -/
def sourceOrthocrossingGridSize (source : PeriodicCNF Nat) : Nat :=
  PeriodicOrthocrossing.drawingGridSize
    (PeriodicCNF.incidenceGraph (sourceFormula source))

/-- Product of all fixed refinements through the final gauged exact-one
placement: planar SAT, retained fan clearance, Figure 9, and unit removal. -/
def horizontalPlacementPeriodFactor : Nat :=
  6 * 12 * 2 * 8 * 36 * 4 * 20

theorem horizontalPlacement_period_eq (source : PeriodicCNF Nat) :
    (horizontalPlacement source).period =
      horizontalPlacementPeriodFactor * sourceOrthocrossingGridSize source := by
  simp only [horizontalPlacement,
    PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    PeriodicVariablePlacement.variableGauge_period,
    PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
    PeriodicOneInThreeNoUnitsPositioned.placement,
    PeriodicOneInThreePositioned.placement,
    PeriodicOrthocrossing.retainedFigureNineClearancePlacement,
    PeriodicVariablePlacement.scale_period,
    PeriodicOrthocrossing.retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceScaledRefinedPlacement,
    PeriodicEightOccurrenceSplit.retainedAngularFanRefinedPlacement,
    PeriodicEightOccurrenceSplitPositioned.placement,
    PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
    PeriodicOrthocrossing.wrappedDrawingPeriodicPlanarSATPlacement,
    PeriodicOrthocrossing.drawingPeriodicPlanarSATPlacement,
    PeriodicOrthocrossing.retainedFigureNineSourceClearanceFactor,
    PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceClearanceFactor,
    PeriodicOrthocrossing.planarMacroScale,
    PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    horizontalPlacementPeriodFactor, sourceOrthocrossingGridSize]
  norm_num [Int.toNat]
  ring

/-- The final exact-one placement period is bounded by an explicit quadratic
function of the source flat-encoding length. -/
theorem horizontalPlacement_period_le_flatLength
    (source : PeriodicCNF Nat) :
    (horizontalPlacement source).period ≤
      horizontalPlacementPeriodFactor *
        (16 * (2 * sourceFormulaPresentationBudget
          (PeriodicCNFFlatEncoding.finEncoding.encode source).length + 1)) := by
  rw [horizontalPlacement_period_eq]
  apply Nat.mul_le_mul_left
  exact (PeriodicCNF.drawingGridSize_incidenceGraph_le_presentationSize
    (sourceFormula source)).trans (Nat.mul_le_mul_left 16 (by
      have sourceSize := sourceFormula_presentationSize_le_flatLength source
      omega))

end PeriodicCNFStripReduction
end LeanTrominoes
