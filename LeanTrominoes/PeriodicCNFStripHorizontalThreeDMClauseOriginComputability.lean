/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedClausePositionComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginData

/-! # Computability of horizontal 3DM clause origins -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalThreeDMClauseOriginComputed_primrec :
    Primrec fun input : PeriodicCNF Nat × Nat =>
      horizontalThreeDMClauseOriginComputed input.1 input.2 := by
  have scaled : Primrec fun input : PeriodicCNF Nat × Nat =>
      Cell.scale 128
        (horizontalNormalizedRoutedClausePositionComputed
          input.1 input.2) :=
    Computability.cell_scale_primrec.comp
      (Primrec.const (128 : Int))
      horizontalNormalizedRoutedClausePositionComputed_primrec
  exact
    (Computability.cell_add_primrec.comp scaled
      (Primrec.const ((50, 60) : Cell))).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
