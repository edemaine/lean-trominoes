/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.StableOccurrenceRankCandidateKeys
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryAlignedAddSemantics
import LeanTrominoes.UnaryFieldBinaryWordCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Stable occurrence keys for arbitrary unary fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldStableOccurrenceKeys

open Computability Turing

/-- Length words exposing equality of arbitrary unary values. -/
def identityWords (values : List Nat) : DelimitedBinaryWords.Input :=
  UnaryFieldBinaryWords.words values

/-- One complete equality row per unary value. -/
def equalityRows (values : List Nat) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWordEqualitySquare.rows (identityWords values)

/-- Stable zero-based occurrence rank of every unary value. -/
def ranks (values : List Nat) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts (equalityRows values)

/-- Reserve three consecutive keys for every unary value. -/
def scaledValues (values : List Nat) : List Nat :=
  UnaryFieldConstantScale.values 3 values

/-- Collision-free base-three key of every occurrence whose multiplicity is
at most three. -/
def keys (values : List Nat) : List Nat :=
  AlignedUnaryListClosure.added (scaledValues values) (ranks values)

theorem equalityRows_words (values : List Nat) :
    (equalityRows values).words =
      (identityWords values).words.map
        (StableOccurrenceRanks.equalityRow (identityWords values).words) := by
  unfold equalityRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  rfl

/-- The machine-oriented prefix counts are the ordinary stable ranks. -/
theorem ranks_eq (values : List Nat) :
    ranks values = StableOccurrenceRanks.ranks values := by
  unfold ranks DelimitedBinaryWordPrefixTrueCounts.counts
  rw [equalityRows_words]
  rw [StableOccurrenceRanks.trueCountsAux_equalityRows]
  unfold identityWords UnaryFieldBinaryWords.words
  exact StableOccurrenceRanks.ranks_map_injective
    values UnaryFieldBinaryWords.word (by
      intro first second wordEq
      have lengthEq := congrArg List.length wordEq
      simpa [UnaryFieldBinaryWords.word] using lengthEq)

@[simp] theorem ranks_length (values : List Nat) :
    (ranks values).length = values.length := by
  rw [ranks_eq]
  exact StableOccurrenceRanks.ranks_length values

@[simp] theorem scaledValues_length (values : List Nat) :
    (scaledValues values).length = values.length := by
  simp [scaledValues, UnaryFieldConstantScale.values]

@[simp] theorem keys_length (values : List Nat) :
    (keys values).length = values.length := by
  simp [keys, AlignedUnaryListClosure.added_length]

private theorem zipWith_scaled (values ranks : List Nat) :
    List.zipWith (fun first second => first + second)
        (values.map fun value => value * 3) ranks =
      List.zipWith (fun value rank => value * 3 + rank) values ranks := by
  induction values generalizing ranks with
  | nil => rfl
  | cons value values induction =>
      cases ranks with
      | nil => rfl
      | cons rank ranks => simp [induction]

/-- The compiled column is exactly the generic stable base-three occurrence
key construction. -/
theorem keys_eq_candidateKeys (values : List Nat) :
    keys values = StableOccurrenceRanks.candidateKeys values := by
  unfold keys scaledValues UnaryFieldConstantScale.values
  rw [ranks_eq]
  unfold AlignedUnaryListClosure.added
    StableOccurrenceRanks.candidateKeys
  have valid : UnaryAlignedAddMachine.Valid
      (values.map fun value => value * 3)
      (StableOccurrenceRanks.ranks values) :=
    UnaryAlignedAddMachine.Valid.of_length_eq (by simp)
  rw [UnaryAlignedAddMachine.sums_eq_zipWith valid]
  exact zipWith_scaled values (StableOccurrenceRanks.ranks values)

noncomputable def identityWordsComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      DelimitedBinaryWords.finEncoding.encode identityWords := by
  unfold identityWords
  exact UnaryFieldBinaryWords.wordsComputableInPolyTime

noncomputable def equalityRowsComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      DelimitedBinaryWords.finEncoding.encode equalityRows := by
  unfold equalityRows
  exact DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields identityWords
    identityWordsComputableInPolyTime

noncomputable def ranksComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields ranks := by
  unfold ranks
  exact TM2CompositionMachine.computableInPolyTime
    equalityRowsComputableInPolyTime
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime

noncomputable def scaledValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields scaledValues := by
  unfold scaledValues
  exact UnaryFieldConstantScale.computableInPolyTime 3

/-- Stable base-three occurrence keys preserve polynomial time for arbitrary
compiled unary columns. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields keys := by
  unfold keys
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    UnaryFieldEncoderMachine.unaryFields scaledValues ranks
    (fun values => by simp)
    scaledValuesComputableInPolyTime ranksComputableInPolyTime

end LeanTrominoes.UnaryFieldStableOccurrenceKeys

end
