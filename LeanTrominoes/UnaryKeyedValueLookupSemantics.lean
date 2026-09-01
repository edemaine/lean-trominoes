/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupSemantics
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics
import LeanTrominoes.UnaryKeyedValueLookupCompiler

/-! # Semantics of repeated unary keyed lookup -/

namespace LeanTrominoes.UnaryKeyedValueLookup

private theorem selected_replicate_true_false
    {Value : Type*} (first second : List Value) :
    DelimitedBinaryWordBooleanFilter.selected
        (List.replicate first.length true ++
          List.replicate second.length false)
        (first ++ second) =
      first := by
  induction first with
  | nil =>
      induction second with
      | nil => rfl
      | cons value second induction =>
          simpa [DelimitedBinaryWordBooleanFilter.selected,
            List.replicate_succ] using induction
  | cons value first induction =>
      simp [DelimitedBinaryWordBooleanFilter.selected,
        List.replicate_succ, induction]

private theorem word_injective :
    Function.Injective UnaryFieldBinaryWords.word := by
  intro first second wordEq
  have lengthEq := congrArg List.length wordEq
  simpa [UnaryFieldBinaryWords.word] using lengthEq

private theorem equalityRow_map_word (source : List Nat) (value : Nat) :
    LastRepresentativeEqualityRows.equalityRow
        (source.map UnaryFieldBinaryWords.word)
        (UnaryFieldBinaryWords.word value) =
      StableOccurrenceRanks.equalityRow source value := by
  unfold LastRepresentativeEqualityRows.equalityRow
    StableOccurrenceRanks.equalityRow
  rw [List.map_map]
  apply List.map_congr_left
  intro other _otherMember
  simp [word_injective.eq_iff]

/-- The Boolean prefix filter keeps every query row, including duplicate
queries, and removes every appended candidate row. -/
theorem queryRows_words (queries candidateKeys : List Nat) :
    (queryRows queries candidateKeys).words =
      queries.map fun query =>
        StableOccurrenceRanks.equalityRow
          (combinedKeys queries candidateKeys) query := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords allRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows
    UnaryFieldBinaryWords.words rowControls combinedKeys
  rw [List.map_append, List.map_append]
  simp only [List.map_map]
  let queryRows := queries.map fun query =>
    LastRepresentativeEqualityRows.equalityRow
      (queries.map UnaryFieldBinaryWords.word ++
        candidateKeys.map UnaryFieldBinaryWords.word)
      (UnaryFieldBinaryWords.word query)
  let candidateRows := candidateKeys.map fun candidate =>
    LastRepresentativeEqualityRows.equalityRow
      (queries.map UnaryFieldBinaryWords.word ++
        candidateKeys.map UnaryFieldBinaryWords.word)
      (UnaryFieldBinaryWords.word candidate)
  change DelimitedBinaryWordBooleanFilter.selected
      (queries.map (fun _ => true) ++
        candidateKeys.map (fun _ => false))
      (queryRows ++ candidateRows) = _
  have queryControls : queries.map (fun _ => true) =
      List.replicate queryRows.length true := by
    simp [queryRows]
  have candidateControls : candidateKeys.map (fun _ => false) =
      List.replicate candidateRows.length false := by
    simp [candidateRows]
  rw [queryControls, candidateControls,
    selected_replicate_true_false]
  unfold queryRows
  apply List.map_congr_left
  intro query _queryMember
  simpa [List.map_append] using
    equalityRow_map_word (queries ++ candidateKeys) query

@[simp] theorem values_length
    (queries candidateKeys candidateValues : List Nat) :
    (values queries candidateKeys candidateValues).length = queries.length := by
  unfold values LastTrueUnaryValueLookupMachine.lookups
  rw [queryRows_words]
  simp

private theorem lookupAux_append
    (candidate : Nat) (firstBits secondBits : List Bool)
    (firstValues secondValues : List Nat)
    (aligned : firstBits.length = firstValues.length) :
    LastTrueUnaryValueLookupMachine.lookupAux candidate
        (firstBits ++ secondBits) (firstValues ++ secondValues) =
      LastTrueUnaryValueLookupMachine.lookupAux
        (LastTrueUnaryValueLookupMachine.lookupAux candidate
          firstBits firstValues)
        secondBits secondValues := by
  induction firstBits generalizing candidate firstValues with
  | nil =>
      have valuesNil : firstValues = [] :=
        List.eq_nil_of_length_eq_zero aligned.symm
      subst firstValues
      rfl
  | cons bit firstBits induction =>
      cases firstValues with
      | nil => simp at aligned
      | cons firstValue firstValues =>
          have tailAligned : firstBits.length = firstValues.length := by
            simpa using aligned
          cases bit with
          | false =>
              simpa [LastTrueUnaryValueLookupMachine.lookupAux] using
                induction (candidate := candidate) firstValues tailAligned
          | true =>
              simpa [LastTrueUnaryValueLookupMachine.lookupAux] using
                induction (candidate := firstValue) firstValues tailAligned

private theorem lookupAux_replicate_zeros (bits : List Bool) :
    LastTrueUnaryValueLookupMachine.lookupAux 0 bits
        (List.replicate bits.length 0) = 0 := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit <;>
        simpa [LastTrueUnaryValueLookupMachine.lookupAux,
          List.replicate_succ] using induction

private theorem lookupAux_equalityRow_zeros
    (source : List Nat) (query : Nat) :
    LastTrueUnaryValueLookupMachine.lookupAux 0
        (StableOccurrenceRanks.equalityRow source query)
        (UnaryFieldConstantStreams.zeros source) = 0 := by
  simpa [StableOccurrenceRanks.equalityRow,
    UnaryFieldConstantStreams.zeros] using
    lookupAux_replicate_zeros
      (StableOccurrenceRanks.equalityRow source query)

/-- The zero-valued query prefix is semantically inert: each query row is
exactly a last-equal-key lookup in the aligned candidate column. -/
theorem lookup_query_eq
    (queries candidateKeys candidateValues : List Nat) (query : Nat) :
    LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow
          (combinedKeys queries candidateKeys) query)
        (paddedValues queries candidateValues) =
      LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow candidateKeys query)
        candidateValues := by
  unfold LastTrueUnaryValueLookupMachine.lookup
    combinedKeys paddedValues StableOccurrenceRanks.equalityRow
  rw [List.map_append,
    lookupAux_append 0
      (queries.map fun other => decide (query = other))
      (candidateKeys.map fun other => decide (query = other))
      (UnaryFieldConstantStreams.zeros queries) candidateValues (by
        simp [UnaryFieldConstantStreams.zeros])]
  change LastTrueUnaryValueLookupMachine.lookupAux
      (LastTrueUnaryValueLookupMachine.lookupAux 0
        (StableOccurrenceRanks.equalityRow queries query)
        (UnaryFieldConstantStreams.zeros queries))
      (StableOccurrenceRanks.equalityRow candidateKeys query)
      candidateValues = _
  rw [lookupAux_equalityRow_zeros]
  rfl

/-- The complete lookup stream is the pointwise last-equal-key selection from
the candidate column, in the original query order. -/
theorem values_eq_map_lookup
    (queries candidateKeys candidateValues : List Nat) :
    values queries candidateKeys candidateValues =
      queries.map fun query =>
        LastTrueUnaryValueLookupMachine.lookup
          (StableOccurrenceRanks.equalityRow candidateKeys query)
          candidateValues := by
  unfold values LastTrueUnaryValueLookupMachine.lookups
  rw [queryRows_words, List.map_map]
  apply List.map_congr_left
  intro query _queryMember
  exact lookup_query_eq queries candidateKeys candidateValues query

/-- If candidate values are a function of their keys and every query key is
present, keyed lookup returns that function pointwise. -/
theorem values_eq_map_datum
    (queries candidateKeys candidateValues : List Nat)
    (datum : Nat → Nat)
    (candidateValuesEq : candidateValues = candidateKeys.map datum)
    (present : ∀ query ∈ queries, query ∈ candidateKeys) :
    values queries candidateKeys candidateValues = queries.map datum := by
  rw [values_eq_map_lookup, candidateValuesEq]
  apply List.map_congr_left
  intro query queryMember
  exact LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
    datum candidateKeys query (present query queryMember)

end LeanTrominoes.UnaryKeyedValueLookup
