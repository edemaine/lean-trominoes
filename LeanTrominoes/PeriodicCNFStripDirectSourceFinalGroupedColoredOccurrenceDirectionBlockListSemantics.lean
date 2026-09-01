/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRoutePairSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockSemantics

/-! # Complete block semantics of grouped colored occurrence directions -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Indexed regrouping selects whole RGB occurrence-direction bodies from
the explicit clause-major source, with every delimiter preserved. -/
theorem directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionTokens decider symbols =
      FiniteAlphabetKeyedDelimitedBlockLookup.expectedBlocks
        (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
          decider symbols)
        (List.range
          (directSourceFinalColoredOccurrenceDirectionBodies
            decider symbols).length)
        (directSourceFinalColoredOccurrenceDirectionBodies
          decider symbols) := by
  unfold directSourceFinalGroupedColoredOccurrenceDirectionTokens
  rw [directSourceFinalColoredOccurrenceDirectionTokens_eq_blocks]
  exact FiniteAlphabetIndexedDelimitedBlockLookup.selected_blocks _ _

end LeanTrominoes.PeriodicCNFStripReduction
