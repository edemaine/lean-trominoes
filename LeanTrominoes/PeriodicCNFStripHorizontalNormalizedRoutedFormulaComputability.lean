/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalPaddedRoutedFormulaComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-! # Executable normalized formula indexing the horizontal 3DM assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Doubled routed positioned formula in the zero-clause-anchor gauge used by
the typed 3DM assembly. -/
def horizontalNormalizedRoutedFormulaComputed
    (source : PeriodicCNF Nat) :=
  (horizontalPaddedRoutedFormulaComputed source).anchorNormalize
    { period := horizontalPaddedRoutedPeriodComputed source
      position := fun _ : RoutedVariable => (0, 0) }

theorem horizontalNormalizedRoutedFormulaComputed_primrec :
    Primrec horizontalNormalizedRoutedFormulaComputed := by
  exact
    PositionedPeriodicCNF.anchorNormalize_primrec
      horizontalPaddedRoutedFormulaComputed
      horizontalPaddedRoutedPeriodComputed
      horizontalPaddedRoutedFormulaComputed_primrec
      horizontalPaddedRoutedPeriodComputed_primrec

/-- Supplying the complete computed placement gives the same normalized
positioned formula: clause-anchor normalization inspects only its period. -/
theorem horizontalNormalizedRoutedFormulaComputed_eq_normalizedSource
    (source : PeriodicCNF Nat) :
    horizontalNormalizedRoutedFormulaComputed source =
      PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource
        ((horizontalRoutedFormulaComputed source).scale 2)
        ((horizontalRoutedPlacementComputed source).scale 2) := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
