/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.UnaryPermutationRankBlockLookupData

/-! # Validity of fixed-width permutation-rank block lookup -/

namespace LeanTrominoes
namespace UnaryPermutationRankBlockLookup

@[simp] theorem paddedValues_length (fieldValues : List Nat) :
    (paddedValues fieldValues).length = 2 * fieldValues.length := by
  simp [paddedValues, UnaryFieldConstantStreams.zeros, two_mul]

theorem expandedRows_forall_length (width : Nat) (ranks : List Nat) :
    (expandedRows width ranks).words.Forall fun row =>
      row.length = (UnaryPermutationRankLookup.extendedRanks ranks).length *
        width := by
  exact DelimitedBinaryWordFixedFieldRowExpansion.rows_forall_length
    width (UnaryPermutationRankLookup.extendedRanks ranks).length
    (UnaryPermutationRankLookup.rankRows ranks)
    (UnaryPermutationRankLookup.rankRows_forall_length ranks)

theorem expandedRows_forall_aligned (width : Nat)
    (ranks fieldValues : List Nat)
    (aligned : fieldValues.length = ranks.length * width) :
    (expandedRows width ranks).words.Forall fun row =>
      row.length = (paddedValues fieldValues).length := by
  have rows := expandedRows_forall_length width ranks
  have extendedLength :
      (UnaryPermutationRankLookup.extendedRanks ranks).length =
        ranks.length + ranks.length := by
    simp [UnaryPermutationRankLookup.extendedRanks,
      UnaryFieldRange.values]
  apply rows.imp
  intro row rowLength
  rw [rowLength, extendedLength, paddedValues_length, aligned]
  simp [Nat.add_mul, two_mul]

/-- Promised input to the generic last-true lookup machine. -/
def input (width : Nat) (ranks fieldValues : List Nat)
    (aligned : fieldValues.length = ranks.length * width) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (expandedRows width ranks).words
  values := paddedValues fieldValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (expandedRows_forall_aligned width ranks fieldValues aligned)

end UnaryPermutationRankBlockLookup
end LeanTrominoes
