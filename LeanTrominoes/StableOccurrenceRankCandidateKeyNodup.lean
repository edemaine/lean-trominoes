/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableOccurrenceRankCandidateKeys

/-! # Uniqueness of bounded stable occurrence keys -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {Value : Type*} [DecidableEq Value]

/-- Base-three occurrence keys recover both components when both ranks are
strictly below three. -/
theorem baseThreeKey_eq_iff
    (firstValue secondValue firstRank secondRank : Nat)
    (firstRankLt : firstRank < 3) (secondRankLt : secondRank < 3) :
    firstValue * 3 + firstRank = secondValue * 3 + secondRank ↔
      firstValue = secondValue ∧ firstRank = secondRank := by
  constructor
  · intro equal
    have residues := congrArg (fun value : Nat => value % 3) equal
    simp [Nat.add_mod, Nat.mod_eq_of_lt firstRankLt,
      Nat.mod_eq_of_lt secondRankLt] at residues
    constructor
    · omega
    · exact residues
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem rank_getElem
    (values : List Value) (index : Nat) (indexLt : index < values.length) :
    (ranks values)[index]'(by simpa using indexLt) =
      (values.take index).count values[index] := by
  have rankIndexLt : index < (ranks values).length := by
    simpa using indexLt
  simpa only [List.getElem?_eq_getElem rankIndexLt,
    List.getElem?_eq_getElem indexLt, Option.map_some,
    Option.some.injEq] using ranks_getElem? values index

/-- Equal values with equal stable ranks occupy the same presentation
position. -/
theorem index_eq_of_value_eq_of_rank_eq
    (values : List Value) (first second : Nat)
    (firstLt : first < values.length) (secondLt : second < values.length)
    (valueEq : values[first] = values[second])
    (rankEq :
      (ranks values)[first]'(by simpa using firstLt) =
        (ranks values)[second]'(by simpa using secondLt)) :
    first = second := by
  have firstRank := rank_getElem values first firstLt
  have secondRank := rank_getElem values second secondLt
  have firstIndex :
      values.idxOfNth values[first]
          ((ranks values)[first]'(by simpa using firstLt)) = first := by
    rw [firstRank, ← List.countBefore_eq_count_take]
    exact List.idxOfNth_countBefore_getElem
  have secondIndex :
      values.idxOfNth values[second]
          ((ranks values)[second]'(by simpa using secondLt)) = second := by
    rw [secondRank, ← List.countBefore_eq_count_take]
    exact List.idxOfNth_countBefore_getElem
  rw [← firstIndex, ← secondIndex, valueEq, rankEq]

/-- Under the semantic multiplicity-three promise, every stable base-three
occurrence key is unique. -/
theorem candidateKeys_nodup_of_count_le_three
    (values : List Nat)
    (atMostThree : ∀ value ∈ values, values.count value ≤ 3) :
    (candidateKeys values).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro first second keyEq
  apply Fin.ext
  have firstValueLt : first.val < values.length := by
    simpa using first.isLt
  have secondValueLt : second.val < values.length := by
    simpa using second.isLt
  have firstRankLt : first.val < (ranks values).length := by
    simpa using firstValueLt
  have secondRankLt : second.val < (ranks values).length := by
    simpa using secondValueLt
  have firstKey :
      (candidateKeys values)[first.val] =
        values[first.val] * 3 + (ranks values)[first.val] := by
    simp [candidateKeys]
  have secondKey :
      (candidateKeys values)[second.val] =
        values[second.val] * 3 + (ranks values)[second.val] := by
    simp [candidateKeys]
  have firstRankEq := rank_getElem values first.val firstValueLt
  have secondRankEq := rank_getElem values second.val secondValueLt
  have firstRankBelowCount :
      (ranks values)[first.val]'firstRankLt <
        values.count values[first.val] := by
    rw [firstRankEq, ← List.countBefore_eq_count_take]
    exact List.countBefore_lt_count_getElem
  have secondRankBelowCount :
      (ranks values)[second.val]'secondRankLt <
        values.count values[second.val] := by
    rw [secondRankEq, ← List.countBefore_eq_count_take]
    exact List.countBefore_lt_count_getElem
  have firstRankBelowThree :
      (ranks values)[first.val]'firstRankLt < 3 :=
    lt_of_lt_of_le firstRankBelowCount
      (atMostThree values[first.val] (List.getElem_mem _))
  have secondRankBelowThree :
      (ranks values)[second.val]'secondRankLt < 3 :=
    lt_of_lt_of_le secondRankBelowCount
      (atMostThree values[second.val] (List.getElem_mem _))
  have components := (baseThreeKey_eq_iff
    values[first.val] values[second.val]
    (ranks values)[first.val] (ranks values)[second.val]
    firstRankBelowThree secondRankBelowThree).mp (by
      simpa only [firstKey, secondKey] using keyEq)
  exact index_eq_of_value_eq_of_rank_eq values first.val second.val
    firstValueLt secondValueLt components.1 components.2

/-- Looking up the base-three key of occurrence rank `rank` recovers the
presentation index of that ranked occurrence. -/
theorem candidateKeys_idxOf_rank
    (values : List Nat)
    (atMostThree : ∀ value ∈ values, values.count value ≤ 3)
    (value rank : Nat) (rankLt : rank < values.count value) :
    (candidateKeys values).idxOf (value * 3 + rank) =
      (values.idxsOf value).getD rank 0 := by
  have rankIndexLt : rank < (values.idxsOf value).length := by
    simpa using rankLt
  let occurrenceIndex := (values.idxsOf value)[rank]
  have occurrenceIndexLt : occurrenceIndex < values.length := by
    exact List.getElem_idxsOf_lt rankIndexLt
  have valueAt : values[occurrenceIndex] = value := by
    have selected := List.getElem_getElem_findIdxs rankIndexLt
    simpa [occurrenceIndex] using selected
  have stableRankAt :
      (ranks values)[occurrenceIndex]'(by simpa using occurrenceIndexLt) =
        rank := by
    have rankListIndexLt : occurrenceIndex < (ranks values).length := by
      simpa using occurrenceIndexLt
    have rankLookup :
        (ranks values)[occurrenceIndex]'rankListIndexLt =
          (values.take occurrenceIndex).count values[occurrenceIndex] := by
      simpa only [List.getElem?_eq_getElem rankListIndexLt,
        List.getElem?_eq_getElem occurrenceIndexLt, Option.map_some,
        Option.some.injEq] using ranks_getElem? values occurrenceIndex
    calc
      _ = (values.take occurrenceIndex).count values[occurrenceIndex] :=
        rankLookup
      _ = (values.take occurrenceIndex).count value := by rw [valueAt]
      _ = rank := by
        rw [show occurrenceIndex =
            (values.idxsOf value)[rank]'rankIndexLt by rfl]
        exact count_take_getElem_idxsOf values value rank rankLt
  have candidateIndexLt :
      occurrenceIndex < (candidateKeys values).length := by
    simpa using occurrenceIndexLt
  have keyAt :
      (candidateKeys values)[occurrenceIndex]'candidateIndexLt =
        value * 3 + rank := by
    simp [candidateKeys, valueAt, stableRankAt]
  have keysNodup := candidateKeys_nodup_of_count_le_three
    values atMostThree
  calc
    (candidateKeys values).idxOf (value * 3 + rank) =
        (candidateKeys values).idxOf
          ((candidateKeys values)[occurrenceIndex]'candidateIndexLt) := by
            rw [keyAt]
    _ = occurrenceIndex :=
      keysNodup.idxOf_getElem occurrenceIndex candidateIndexLt
    _ = (values.idxsOf value).getD rank 0 := by
      rw [List.getD_eq_getElem _ _ rankIndexLt]

end LeanTrominoes.StableOccurrenceRanks
