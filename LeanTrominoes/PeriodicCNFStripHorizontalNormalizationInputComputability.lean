/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingComputability

/-! # Computability of the horizontal rectangular-normalization input -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalNormalizationInputComputed_primrec :
    Primrec horizontalNormalizationInputComputed := by
  unfold horizontalNormalizationInputComputed
  exact
    (PeriodicThreeDM.NormalizationCompiler.Input.equivData_symm_primrec.comp
      (Primrec.pair horizontalThreeDMProblemComputed_primrec
        horizontalThreeDMDrawingComputed_primrec))

theorem horizontalNormalizationInputComputed_computable :
    Computable horizontalNormalizationInputComputed :=
  horizontalNormalizationInputComputed_primrec.to_comp

end PeriodicCNFStripReduction
end LeanTrominoes
