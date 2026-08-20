/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizationInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizationInputSemanticBridge

/-! # Computability of the certified strip-normalization input -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The normalization input extracted from the proof-backed planar
presentation is computable through its extensionally equal data compiler. -/
theorem normalizationInput_computable : Computable normalizationInput := by
  exact horizontalNormalizationInputComputed_computable.of_eq
    horizontalNormalizationInputComputed_eq_normalizationInput

end PeriodicCNFStripReduction
end LeanTrominoes
