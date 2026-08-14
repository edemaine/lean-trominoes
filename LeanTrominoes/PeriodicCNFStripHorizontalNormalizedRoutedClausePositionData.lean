/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability

/-! # Clause-position lookup in the executable normalized 3DM source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

def horizontalNormalizedRoutedClausePositionComputed
    (source : PeriodicCNF Nat) (clauseIndex : Nat) : Cell :=
  (horizontalNormalizedRoutedFormulaComputed source).clausePosition
    clauseIndex

end PeriodicCNFStripReduction
end LeanTrominoes
