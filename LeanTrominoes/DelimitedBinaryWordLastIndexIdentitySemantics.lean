/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLastIndexIdentityCompiler
import LeanTrominoes.LastTrueUnaryValueLookupSemantics

/-! # Semantics of canonical last-index word identities -/

namespace LeanTrominoes

namespace LastTrueUnaryValueLookupMachine

variable {Value : Type*} [DecidableEq Value]

/-- Looking up presentation indices along an equality row selects the index
of an occurrence of the target. -/
theorem lookupAux_equalityRow_range'_selected
    (candidate start : Nat) (values : List Value) (target : Value)
    (targetMem : target ∈ values) :
    ∃ index, ∃ indexLt : index < values.length,
      lookupAux candidate
          (StableOccurrenceRanks.equalityRow values target)
          (List.range' start values.length) =
        start + index ∧
      values[index]'indexLt = target := by
  induction values generalizing candidate start with
  | nil => simp at targetMem
  | cons value values induction =>
      simp only [List.length_cons]
      rw [List.range'_succ]
      by_cases same : target = value
      · subst value
        by_cases later : target ∈ values
        · obtain ⟨index, indexLt, lookupEq, valueEq⟩ :=
            induction start (start + 1) later
          refine ⟨index + 1, by omega, ?_, ?_⟩
          · simpa [StableOccurrenceRanks.equalityRow, lookupAux,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lookupEq
          · simpa using valueEq
        · refine ⟨0, by simp, ?_, by simp⟩
          simpa [StableOccurrenceRanks.equalityRow, lookupAux] using
            lookupAux_equalityRow_of_not_mem start target values
              (List.range' (start + 1) values.length) later
      · have later : target ∈ values := by
          simpa [same] using targetMem
        obtain ⟨index, indexLt, lookupEq, valueEq⟩ :=
          induction candidate (start + 1) later
        refine ⟨index + 1, by omega, ?_, ?_⟩
        · simpa [StableOccurrenceRanks.equalityRow, lookupAux, same,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lookupEq
        · simpa using valueEq

/-- Public zero-based form of index selection. -/
theorem lookup_equalityRow_range_selected
    (values : List Value) (target : Value) (targetMem : target ∈ values) :
    ∃ index, ∃ indexLt : index < values.length,
      lookup (StableOccurrenceRanks.equalityRow values target)
          (List.range values.length) = index ∧
      values[index]'indexLt = target := by
  simpa [lookup, List.range_eq_range'] using
    lookupAux_equalityRow_range'_selected 0 0 values target targetMem

/-- Two represented values have the same last matching presentation index
exactly when they are equal. -/
theorem lookup_equalityRow_range_eq_iff
    (values : List Value) (first second : Value)
    (firstMem : first ∈ values) (secondMem : second ∈ values) :
    lookup (StableOccurrenceRanks.equalityRow values first)
          (List.range values.length) =
        lookup (StableOccurrenceRanks.equalityRow values second)
          (List.range values.length) ↔
      first = second := by
  constructor
  · intro lookupEq
    obtain ⟨firstIndex, _firstIndexLt, firstLookup, firstValue⟩ :=
      lookup_equalityRow_range_selected values first firstMem
    obtain ⟨secondIndex, _secondIndexLt, secondLookup, secondValue⟩ :=
      lookup_equalityRow_range_selected values second secondMem
    have indexEq : firstIndex = secondIndex :=
      firstLookup.symm.trans (lookupEq.trans secondLookup)
    have firstLookupValue : values[firstIndex]? = some first := by
      rw [List.getElem?_eq_getElem _firstIndexLt, firstValue]
    have secondLookupValue : values[secondIndex]? = some second := by
      rw [List.getElem?_eq_getElem _secondIndexLt, secondValue]
    rw [indexEq] at firstLookupValue
    exact Option.some.inj (firstLookupValue.symm.trans secondLookupValue)
  · rintro rfl
    rfl

end LastTrueUnaryValueLookupMachine

namespace DelimitedBinaryWordLastIndexIdentity

/-- Canonical identities are the last matching presentation indices of the
semantic word list. -/
theorem identityIndices_eq_map (input : DelimitedBinaryWords.Input) :
    identityIndices input =
      input.words.map fun word =>
        LastTrueUnaryValueLookupMachine.lookup
          (LastRepresentativeEqualityRows.equalityRow input.words word)
          (List.range input.words.length) := by
  unfold identityIndices LastTrueUnaryValueLookupMachine.lookups
  change (equalityRows input).words.map (fun row =>
      LastTrueUnaryValueLookupMachine.lookup row (positionValues input)) = _
  unfold equalityRows positionValues
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  simp [LastRepresentativeEqualityRows.equalityRows]

/-- Two positions receive the same numeric identity exactly when their
binary words are equal. -/
theorem identityIndices_getElem_eq_iff
    (input : DelimitedBinaryWords.Input) (first second : Nat)
    (firstLt : first < input.words.length)
    (secondLt : second < input.words.length) :
    (identityIndices input)[first]'(by simpa using firstLt) =
        (identityIndices input)[second]'(by simpa using secondLt) ↔
      input.words[first] = input.words[second] := by
  have firstIdentity :
      (identityIndices input)[first]'(by simpa using firstLt) =
        LastTrueUnaryValueLookupMachine.lookup
          (LastRepresentativeEqualityRows.equalityRow input.words
            input.words[first])
          (List.range input.words.length) := by
    have pointwise := congrArg (fun values => values[first]?)
      (identityIndices_eq_map input)
    have identityLt : first < (identityIndices input).length := by
      simpa using firstLt
    rw [List.getElem?_eq_getElem identityLt] at pointwise
    simp only [List.getElem?_map,
      List.getElem?_eq_getElem firstLt, Option.map_some] at pointwise
    exact Option.some.inj pointwise
  have secondIdentity :
      (identityIndices input)[second]'(by simpa using secondLt) =
        LastTrueUnaryValueLookupMachine.lookup
          (LastRepresentativeEqualityRows.equalityRow input.words
            input.words[second])
          (List.range input.words.length) := by
    have pointwise := congrArg (fun values => values[second]?)
      (identityIndices_eq_map input)
    have identityLt : second < (identityIndices input).length := by
      simpa using secondLt
    rw [List.getElem?_eq_getElem identityLt] at pointwise
    simp only [List.getElem?_map,
      List.getElem?_eq_getElem secondLt, Option.map_some] at pointwise
    exact Option.some.inj pointwise
  rw [firstIdentity, secondIdentity]
  simpa [LastRepresentativeEqualityRows.equalityRow,
    StableOccurrenceRanks.equalityRow] using
    LastTrueUnaryValueLookupMachine.lookup_equalityRow_range_eq_iff
      input.words input.words[first] input.words[second]
      (List.getElem_mem firstLt) (List.getElem_mem secondLt)

end DelimitedBinaryWordLastIndexIdentity

end LeanTrominoes
