/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCountPredCompiler
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Components recovered from stable occurrence keys -/

namespace LeanTrominoes.StableOccurrenceRanks

/-- At a present candidate key's unique position, integer quotient and
remainder recover its original identity and stable rank. -/
theorem candidateKey_getD_components
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (key : Nat) (keyMember : key ∈ candidateKeys values) :
    let index := (candidateKeys values).idxOf key
    values.getD index 0 = key / 3 ∧
      (ranks values).getD index 0 = key % 3 := by
  let index := (candidateKeys values).idxOf key
  have indexLt : index < (candidateKeys values).length :=
    List.idxOf_lt_length_iff.mpr keyMember
  have valueIndexLt : index < values.length := by
    simpa using indexLt
  have rankIndexLt : index < (ranks values).length := by
    simpa using valueIndexLt
  have keyAt : (candidateKeys values)[index] = key :=
    List.getElem_idxOf indexLt
  have rankEq :
      (ranks values)[index] =
        (values.take index).count values[index] := by
    simpa only [List.getElem?_eq_getElem rankIndexLt,
      List.getElem?_eq_getElem valueIndexLt,
      Option.map_some, Option.some.injEq] using
      ranks_getElem? values index
  have rankLt :
      (ranks values)[index] < values.count values[index] := by
    rw [rankEq]
    exact @List.count_getElem_take_lt_count Nat _ (by infer_instance)
      values index valueIndexLt
  have rankThree : (ranks values)[index] < 3 :=
    lt_of_lt_of_le rankLt
      (countLe values[index] (List.getElem_mem valueIndexLt))
  have encoded : values[index] * 3 + (ranks values)[index] = key := by
    simpa [candidateKeys] using keyAt
  constructor
  · rw [List.getD_eq_getElem _ _ valueIndexLt]
    omega
  · rw [List.getD_eq_getElem _ _ rankIndexLt]
    omega

/-- Looking up a bounded multiplicity predecessor beside a present candidate
key recovers the predecessor of the identity named by its quotient. -/
theorem alignedCountPred_eq
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (key : Nat) (keyMember : key ∈ candidateKeys values) :
    FiniteAlphabetKeyedValueLookup.alignedDatum
        (candidateKeys values)
        (values.map fun value =>
          BoundedPositiveCountPreds.boundedPositiveCountPred
            (values.count value)) key =
      BoundedPositiveCountPreds.boundedPositiveCountPred
        (values.count (key / 3)) := by
  have components := candidateKey_getD_components
    values countLe key keyMember
  have indexLt : (candidateKeys values).idxOf key < values.length := by
    rw [← candidateKeys_length]
    exact List.idxOf_lt_length_iff.mpr keyMember
  unfold FiniteAlphabetKeyedValueLookup.alignedDatum
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt),
    List.getElem_map]
  have valueEq := components.1
  rw [List.getD_eq_getElem _ _ indexLt] at valueEq
  rw [valueEq]

end LeanTrominoes.StableOccurrenceRanks
