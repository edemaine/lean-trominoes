/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability

/-! # Semantic bridge for the normalized horizontal ribbon source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalNormalizedRoutedFormulaComputed_eq_semanticData
    (source : PeriodicCNF Nat) :
    horizontalNormalizedRoutedFormulaComputed source =
      horizontalSemanticNormalizedRibbonSource source := by
  rw [horizontalNormalizedRoutedFormulaComputed_eq_normalizedSource,
    horizontalRoutedFormulaComputed_eq_semanticData,
    horizontalRoutedPlacementComputed_eq_semanticData]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
