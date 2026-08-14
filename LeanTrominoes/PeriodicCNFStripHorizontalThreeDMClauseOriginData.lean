/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedClausePositionData

/-! # Executable clause-origin data of the horizontal 3DM assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Origin of the fixed clause gadget inside its `128 × 128` macrocell. -/
def horizontalThreeDMClauseOriginComputed
    (source : PeriodicCNF Nat) (clauseIndex : Nat) : Cell :=
  Cell.add
    (Cell.scale 128
      (horizontalNormalizedRoutedClausePositionComputed
        source clauseIndex))
    (50, 60)

end PeriodicCNFStripReduction
end LeanTrominoes
