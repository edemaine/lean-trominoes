/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRoutePairSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeySemantics

/-! # Complete block semantics of grouped colored occurrence directions -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Exact query-major body list selected by the variable-major RGB block
ordinals. -/
noncomputable def directSourceFinalGroupedColoredOccurrenceDirectionBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList
    (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
      decider symbols)
    (List.range
      (directSourceFinalColoredOccurrenceDirectionBodies
        decider symbols).length)
    (directSourceFinalColoredOccurrenceDirectionBodies decider symbols)

/-- Every compiled RGB block ordinal names a genuine clause-major colored
occurrence body. -/
theorem directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinal_lt
    (symbols : List encoding.Γ) (ordinal : Nat)
    (member : ordinal ∈
      directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
        decider symbols) :
    ordinal <
      (directSourceFinalColoredOccurrenceDirectionBodies
        decider symbols).length := by
  rw [directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_eq]
    at member
  obtain ⟨index, indexMember, ordinalMember⟩ :=
    List.mem_flatMap.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ordinalMember
  have indexLt := directSourceFinalGroupedOccurrenceIndex_lt
    decider symbols index indexMember
  rw [directSourceFinalColoredOccurrenceDirectionBodies_length]
  rcases ordinalMember with rfl | rfl | rfl <;> omega

@[simp] theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBodies_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies
      decider symbols).length =
      3 * (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedColoredOccurrenceDirectionBodies
  rw [FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList_length]
  · exact
      directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals_length
        decider symbols
  · simp
  · exact List.nodup_range
  · intro ordinal member
    exact List.mem_range.mpr
      (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinal_lt
        decider symbols ordinal member)

/-- The grouped routed-incidence key column is aligned one-for-one with the
explicit grouped direction bodies. -/
theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBodies_length_eq_keys
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies
      decider symbols).length =
      (directSourceFinalGroupedRoutedIncidenceKeys decider symbols).length := by
  rw [directSourceFinalGroupedColoredOccurrenceDirectionBodies_length,
    directSourceFinalGroupedRoutedIncidenceKeys_length,
    directSourceFinalGroupedOccurrenceData_length]

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

/-- Equivalently, the regrouped token stream is serialization of the exact
selected body list. -/
theorem directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_bodyList
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (directSourceFinalGroupedColoredOccurrenceDirectionBodies
          decider symbols) := by
  rw [directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_blocks]
  exact FiniteAlphabetKeyedDelimitedBlockLookup.expectedBlocks_eq_blocks
    _ _ _

end LeanTrominoes.PeriodicCNFStripReduction
