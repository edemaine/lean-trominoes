/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsFirstTrueCompiler
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Unary field lookup in permutation-rank order -/

namespace LeanTrominoes
namespace UnaryPermutationRankLookup

/-- Append a canonical occurrence of every possible rank.  Last-occurrence
representative selection will consequently enumerate ranks in increasing
order whenever the original ranks form a permutation. -/
def extendedRanks (ranks : List Nat) : List Nat :=
  ranks ++ UnaryFieldRange.values ranks

/-- Equality rows in last-occurrence rank order, with all but the first true
bit cleared. -/
def rankRows (ranks : List Nat) : DelimitedBinaryWords.Input :=
  ⟨(extendedRanks ranks).dedup.map fun rank =>
    DelimitedBinaryWordsFirstTrue.row
      (LastRepresentativeEqualityRows.equalityRow
        (extendedRanks ranks) rank)⟩

/-- Original field values followed by one zero sentinel for every appended
canonical rank. -/
def paddedValues (ranks fieldValues : List Nat) : List Nat :=
  fieldValues ++ UnaryFieldConstantStreams.zeros ranks

@[simp] theorem firstTrue_rowAux_length (seen : Bool) (bits : List Bool) :
    (DelimitedBinaryWordsFirstTrue.rowAux seen bits).length = bits.length := by
  induction bits generalizing seen with
  | nil => rfl
  | cons bit bits induction =>
      simp [DelimitedBinaryWordsFirstTrue.rowAux, induction]

@[simp] theorem firstTrue_row_length (bits : List Bool) :
    (DelimitedBinaryWordsFirstTrue.row bits).length = bits.length := by
  simp [DelimitedBinaryWordsFirstTrue.row]

@[simp] theorem equalityRow_length (values : List Nat) (value : Nat) :
    (LastRepresentativeEqualityRows.equalityRow values value).length =
      values.length := by
  simp [LastRepresentativeEqualityRows.equalityRow]

@[simp] theorem rankRows_forall_length (ranks : List Nat) :
    (rankRows ranks).words.Forall fun row =>
      row.length = (extendedRanks ranks).length := by
  rw [List.forall_iff_forall_mem]
  intro row rowMember
  obtain ⟨rank, _rankMember, rfl⟩ := List.mem_map.mp rowMember
  simp

@[simp] theorem paddedValues_length (ranks fieldValues : List Nat)
    (aligned : fieldValues.length = ranks.length) :
    (paddedValues ranks fieldValues).length =
      (extendedRanks ranks).length := by
  simp [paddedValues, extendedRanks, UnaryFieldConstantStreams.zeros,
    UnaryFieldRange.values, aligned]

/-- Promised input to the generic last-true lookup machine. -/
def input (ranks fieldValues : List Nat)
    (aligned : fieldValues.length = ranks.length) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (rankRows ranks).words
  values := paddedValues ranks fieldValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    ((rankRows_forall_length ranks).imp fun _row rowLength =>
      rowLength.trans (paddedValues_length ranks fieldValues aligned).symm)

/-- Look up the field belonging to each last-occurrence-ordered rank. -/
def values (ranks fieldValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (rankRows ranks).words (paddedValues ranks fieldValues)

end UnaryPermutationRankLookup
end LeanTrominoes
