/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedClausePositionData

/-! # Computability of normalized horizontal clause-position lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalNormalizedRoutedClausePositionComputed_primrec :
    Primrec fun input : PeriodicCNF Nat × Nat =>
      horizontalNormalizedRoutedClausePositionComputed input.1 input.2 := by
  exact
    (PositionedPeriodicCNF.clausePosition_primrec.comp
      (Primrec.pair
        (horizontalNormalizedRoutedFormulaComputed_primrec.comp Primrec.fst)
        Primrec.snd)).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
