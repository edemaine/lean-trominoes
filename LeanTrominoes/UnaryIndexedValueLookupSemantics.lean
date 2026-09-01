/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupSemantics
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Semantics of repeated unary indexed lookup -/

namespace LeanTrominoes.UnaryIndexedValueLookup

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
theorem queryRows_words (queries candidateValues : List Nat) :
    (queryRows queries candidateValues).words =
      queries.map fun query =>
        StableOccurrenceRanks.equalityRow
          (combinedKeys queries candidateValues) query := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords allRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows
    UnaryFieldBinaryWords.words rowControls combinedKeys
  rw [List.map_append, List.map_append]
  simp only [List.map_map]
  let queryRows := queries.map fun query =>
    LastRepresentativeEqualityRows.equalityRow
      (queries.map UnaryFieldBinaryWords.word ++
        (candidateKeys candidateValues).map UnaryFieldBinaryWords.word)
      (UnaryFieldBinaryWords.word query)
  let candidateRows := (candidateKeys candidateValues).map fun candidate =>
    LastRepresentativeEqualityRows.equalityRow
      (queries.map UnaryFieldBinaryWords.word ++
        (candidateKeys candidateValues).map UnaryFieldBinaryWords.word)
      (UnaryFieldBinaryWords.word candidate)
  change DelimitedBinaryWordBooleanFilter.selected
      (queries.map (fun _ => true) ++
        candidateValues.map (fun _ => false))
      (queryRows ++ candidateRows) = _
  have queryControls : queries.map (fun _ => true) =
      List.replicate queryRows.length true := by
    simp [queryRows]
  have candidateControls : candidateValues.map (fun _ => false) =
      List.replicate candidateRows.length false := by
    simp [candidateRows, candidateKeys]
  rw [queryControls, candidateControls,
    selected_replicate_true_false]
  unfold queryRows
  apply List.map_congr_left
  intro query _queryMember
  simpa [List.map_append] using
    equalityRow_map_word (queries ++ candidateKeys candidateValues) query

@[simp] theorem values_length (queries candidateValues : List Nat) :
    (values queries candidateValues).length = queries.length := by
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

/-- One valid query selects exactly the candidate value at that index. -/
theorem lookup_query_eq_getD (queries candidateValues : List Nat)
    (query : Nat) (queryLt : query < candidateValues.length) :
    LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow
          (combinedKeys queries candidateValues) query)
        (paddedValues queries candidateValues) =
      candidateValues.getD query 0 := by
  have queryMember : query ∈ candidateKeys candidateValues := by
    exact List.mem_range.mpr queryLt
  let prefixCandidate :=
    LastTrueUnaryValueLookupMachine.lookupAux 0
      (StableOccurrenceRanks.equalityRow queries query)
      (UnaryFieldConstantStreams.zeros queries)
  have irrelevant :=
    LastTrueUnaryValueLookupMachine.lookupAux_equalityRow_candidate_irrelevant
      prefixCandidate 0 query (candidateKeys candidateValues)
      candidateValues queryMember
  have selected := LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
    (fun index => candidateValues.getD index 0)
    (candidateKeys candidateValues) query queryMember
  have mappedValues :
      (candidateKeys candidateValues).map
          (fun index => candidateValues.getD index 0) =
        candidateValues := by
    exact List.map_range_getD candidateValues 0
  rw [mappedValues] at selected
  unfold LastTrueUnaryValueLookupMachine.lookup at selected ⊢
  unfold combinedKeys paddedValues
  rw [StableOccurrenceRanks.equalityRow]
  rw [List.map_append]
  rw [lookupAux_append 0
    (queries.map fun other => decide (query = other))
    ((candidateKeys candidateValues).map fun other =>
      decide (query = other))
    (UnaryFieldConstantStreams.zeros queries) candidateValues (by
      simp [UnaryFieldConstantStreams.zeros])]
  change LastTrueUnaryValueLookupMachine.lookupAux prefixCandidate
      (StableOccurrenceRanks.equalityRow
        (candidateKeys candidateValues) query)
      candidateValues = _
  exact irrelevant.trans selected

/-- When all queries are in range, the compiled lookup is pointwise ordinary
zero-based list lookup in the original query order. -/
theorem values_eq_map_getD_of_forall_lt
    (queries candidateValues : List Nat)
    (valid : ∀ query ∈ queries, query < candidateValues.length) :
    values queries candidateValues =
      queries.map fun query => candidateValues.getD query 0 := by
  unfold values LastTrueUnaryValueLookupMachine.lookups
  rw [queryRows_words]
  rw [List.map_map]
  apply List.map_congr_left
  intro query queryMember
  exact lookup_query_eq_getD queries candidateValues query
    (valid query queryMember)

end LeanTrominoes.UnaryIndexedValueLookup
