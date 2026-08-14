/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMPeriodComputability

/-! # Semantic identification of the executable horizontal 3DM period -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedPlacementSourceVariableDecidableEq

/-- The scalar period expression occurring in the retained padded 3DM
presentation, with the fixed three-strand factor reduced to `128`. -/
def horizontalThreeDMPeriodSemantic (source : PeriodicCNF Nat) : Nat :=
  128 *
    (2 *
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinementFactor *
        (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (sourceFormula source)).period))

theorem horizontalThreeDMPeriodComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalThreeDMPeriodComputed source =
      horizontalThreeDMPeriodSemantic source := by
  unfold horizontalThreeDMPeriodComputed horizontalThreeDMPeriodSemantic
  rw [horizontalRoutedPlacementComputed_eq_semantic]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
