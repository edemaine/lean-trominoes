/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics

/-! # Semantics of variable-major colored occurrence directions -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled block queries are the three consecutive original block
ordinals for every selected clause-major occurrence position. -/
theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_eq
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
        decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).flatMap
        fun index => [3 * index, 3 * index + 1, 3 * index + 2] := by
  unfold directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
  exact UnaryFieldThreeBlockOrdinals.values_eq_flatMap _

@[simp] theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
      decider symbols).length =
      3 * (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_eq]
  simp [directSourceFinalGroupedOccurrenceIndices_length, Nat.mul_comm]

/-- The reordered output is exactly query-major selection of every token in
the requested original delimited block. -/
@[simp] theorem
    directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionTokens decider symbols =
      FiniteAlphabetIndexedDelimitedBlockLookup.expected
        (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
          decider symbols)
        (directSourceFinalColoredOccurrenceDirectionTokens
          decider symbols) := by
  unfold directSourceFinalGroupedColoredOccurrenceDirectionTokens
  exact FiniteAlphabetIndexedDelimitedBlockLookup.selected_eq_expected _ _

end LeanTrominoes.PeriodicCNFStripReduction
