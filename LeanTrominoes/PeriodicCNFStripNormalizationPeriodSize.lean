/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripPresentationPeriod
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerPeriod

/-!
# Final rectangular-normalization period bound
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- Product of every fixed geometric refinement from orthocrossing through
the three final normalization rounds. -/
def normalizationPeriodFactor : Nat :=
  PeriodicThreeDM.vertexNormalizationScaleNat ^ 3 *
    PeriodicPlanarOneInThreeToThreeDM.standardThreeStrandLayout.factor *
      2 *
        PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinementFactor *
          horizontalPlacementPeriodFactor

theorem normalizationInput_finalNormalizationPeriod_eq
    (source : PeriodicCNF Nat) :
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
      (normalizationInput source) =
        normalizationPeriodFactor * sourceOrthocrossingGridSize source := by
  rw [normalizationInput,
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod_inputOfPresentation,
    presentation_drawing_gridSize_eq,
    horizontalPlacement_period_eq]
  unfold normalizationPeriodFactor
  ring

/-- Explicit source-length budget for the final normalization period. -/
def normalizationPeriodBudget (sourceFlatLength : Nat) : Nat :=
  normalizationPeriodFactor *
    (16 * (2 * sourceFormulaPresentationBudget sourceFlatLength + 1))

theorem normalizationInput_finalNormalizationPeriod_le_flatLength
    (source : PeriodicCNF Nat) :
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
        (normalizationInput source) ≤
      normalizationPeriodBudget
        (PeriodicCNFFlatEncoding.finEncoding.encode source).length := by
  rw [normalizationInput_finalNormalizationPeriod_eq]
  unfold normalizationPeriodBudget
  have sourceSize := sourceFormula_presentationSize_le_flatLength source
  have inside :
      2 * PeriodicCNF.presentationSize (sourceFormula source) + 1 ≤
        2 * sourceFormulaPresentationBudget
          (PeriodicCNFFlatEncoding.finEncoding.encode source).length + 1 := by
    omega
  have grid :=
    PeriodicCNF.drawingGridSize_incidenceGraph_le_presentationSize
      (sourceFormula source)
  have gridBudget : sourceOrthocrossingGridSize source ≤
      16 * (2 * sourceFormulaPresentationBudget
        (PeriodicCNFFlatEncoding.finEncoding.encode source).length + 1) := by
    simpa only [sourceOrthocrossingGridSize] using
      grid.trans (Nat.mul_le_mul_left 16 inside)
  exact Nat.mul_le_mul_left normalizationPeriodFactor
    gridBudget

end PeriodicCNFStripReduction
end LeanTrominoes
