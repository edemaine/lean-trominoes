/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupCompiler
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics

/-! # Exact semantics of binary-word keyed unary-value lookup -/

namespace LeanTrominoes.DelimitedBinaryWordKeyedValueLookup

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


/-- Every query keeps its equality row, even when query words repeat. -/
theorem queryRows_words (queries candidates : DelimitedBinaryWords.Input) :
    (queryRows queries candidates).words =
      queries.words.map (StableOccurrenceRanks.equalityRow
        (queries.words ++ candidates.words)) := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows rowControls
  simp only [DelimitedBinaryWords.append_words, List.map_append]
  have queryControls : queries.words.map (fun _ => true) =
      List.replicate
        (queries.words.map (LastRepresentativeEqualityRows.equalityRow
          (queries.words ++ candidates.words))).length true := by simp
  have candidateControls : candidates.words.map (fun _ => false) =
      List.replicate
        (candidates.words.map (LastRepresentativeEqualityRows.equalityRow
          (queries.words ++ candidates.words))).length false := by simp
  rw [queryControls, candidateControls, selected_replicate_true_false]
  rfl

@[simp] theorem values_length (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) :
    (values queries candidates candidateValues).length = queries.words.length := by
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


/-- Query-prefix padding contributes no value; only candidate columns matter. -/
theorem lookup_query_eq (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) (query : List Bool) :
    LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow (queries.words ++ candidates.words) query)
        (paddedValues queries candidateValues) =
      LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow candidates.words query) candidateValues := by
  unfold LastTrueUnaryValueLookupMachine.lookup paddedValues
    StableOccurrenceRanks.equalityRow
  rw [List.map_append, lookupAux_append 0 _ _ _ _ (by simp)]
  have zeroPrefix := lookupAux_replicate_zeros
    (queries.words.map fun other => decide (query = other))
  simp only [List.length_map] at zeroPrefix
  rw [zeroPrefix]

/-- Exact pointwise last-equal-candidate selection, including missing keys. -/
theorem values_eq_map_lookup (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) :
    values queries candidates candidateValues = queries.words.map fun query =>
      LastTrueUnaryValueLookupMachine.lookup
        (StableOccurrenceRanks.equalityRow candidates.words query) candidateValues := by
  unfold values LastTrueUnaryValueLookupMachine.lookups
  rw [queryRows_words, List.map_map]
  apply List.map_congr_left
  intro query _member
  exact lookup_query_eq queries candidates candidateValues query

/-- Values determined by keys are recovered exactly; absent keys return zero. -/
theorem values_map_datum (queries candidates : DelimitedBinaryWords.Input)
    (datum : List Bool → Nat) :
    values queries candidates (candidates.words.map datum) =
      queries.words.map fun query => if query ∈ candidates.words then datum query else 0 := by
  rw [values_eq_map_lookup]
  apply List.map_congr_left
  intro query _member
  by_cases member : query ∈ candidates.words
  · rw [if_pos member]
    exact LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
      datum candidates.words query member
  · rw [if_neg member]
    exact LastTrueUnaryValueLookupMachine.lookupAux_equalityRow_of_not_mem
      0 query candidates.words (candidates.words.map datum) member

/-- Semantic key equality need only be reflected between query and candidate
objects. The compiler then recovers any aligned datum on present objects. -/
theorem values_map_keys
    {Atom : Type} [DecidableEq Atom] (queries candidates : List Atom)
    (key : Atom → List Bool) (datum : Atom → Nat)
    (reflects : ∀ query ∈ queries, ∀ candidate ∈ candidates,
      key query = key candidate → query = candidate) :
    values ⟨queries.map key⟩ ⟨candidates.map key⟩ (candidates.map datum) =
      queries.map fun query => if query ∈ candidates then datum query else 0 := by
  rw [values_eq_map_lookup, List.map_map]
  apply List.map_congr_left
  intro query queryMember
  have rowEq : StableOccurrenceRanks.equalityRow (candidates.map key) (key query) =
      StableOccurrenceRanks.equalityRow candidates query := by
    unfold StableOccurrenceRanks.equalityRow
    rw [List.map_map]
    apply List.map_congr_left
    intro candidate candidateMember
    have equal : (key query = key candidate) ↔ query = candidate :=
      ⟨reflects query queryMember candidate candidateMember, congrArg key⟩
    simp [equal]
  dsimp only [Function.comp_def]
  rw [rowEq]
  by_cases member : query ∈ candidates
  · rw [if_pos member]
    exact LastTrueUnaryValueLookupMachine.lookup_equalityRow_map datum candidates query member
  · rw [if_neg member]
    exact LastTrueUnaryValueLookupMachine.lookupAux_equalityRow_of_not_mem
      0 query candidates (candidates.map datum) member

end LeanTrominoes.DelimitedBinaryWordKeyedValueLookup
