/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StrictListRankLookupData

/-! # Correctness of unsorted strict-rank lookup -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

private theorem find?_eq_some_of_mem_of_unique
    (values : List Value) (predicate : Value → Bool) (selected : Value)
    (member : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (unique : ∀ candidate ∈ values,
      predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      by_cases headTrue : predicate head = true
      · have headEq : head = selected :=
          unique head (by simp) headTrue
        subst head
        simp [selectedTrue]
      · have selectedTail : selected ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with selectedEq | selectedTail
          · subst head
            exact (headTrue selectedTrue).elim
          · exact selectedTail
        rw [List.find?_cons_of_neg headTrue]
        exact induction selectedTail fun candidate
          candidateMember candidateTrue =>
            unique candidate (by simp [candidateMember]) candidateTrue

/-- Unsorted lower-rank lookup returns exactly the value stored at that
index in the strictly ordered insertion sort. -/
theorem valueAtLowerRank?_eq_sorted_getElem?
    (coordinate : Value → Coordinate) (values : List Value)
    (ordered :
      (values.insertionSort fun first second =>
        coordinate first ≤ coordinate second).Pairwise fun first second =>
          coordinate first < coordinate second)
    (index : Nat) (value : Value)
    (lookup :
      (values.insertionSort fun first second =>
        coordinate first ≤ coordinate second)[index]? = some value) :
    valueAtLowerRank? coordinate values index = some value := by
  let sorted := values.insertionSort fun first second =>
    coordinate first ≤ coordinate second
  have valueMember : value ∈ values := by
    rw [← List.mem_insertionSort
      (r := fun first second => coordinate first ≤ coordinate second)]
    exact List.mem_of_getElem? lookup
  apply find?_eq_some_of_mem_of_unique
    values
    (fun candidate => lowerRank coordinate values candidate = index)
    value valueMember
  · simp only [decide_eq_true_eq]
    exact lowerRank_eq_sortedIndex_of_getElem?
      coordinate values ordered index value lookup
  · intro candidate candidateMember candidateRank
    simp only [decide_eq_true_eq] at candidateRank
    have candidateSortedMember : candidate ∈ sorted := by
      exact (List.mem_insertionSort
        (r := fun first second => coordinate first ≤ coordinate second)).mpr
          candidateMember
    rcases List.mem_iff_getElem?.mp candidateSortedMember with
      ⟨candidateIndex, candidateLookup⟩
    have candidateIndexEq : candidateIndex = index := by
      rw [← lowerRank_eq_sortedIndex_of_getElem?
        coordinate values ordered candidateIndex candidate candidateLookup]
      exact candidateRank
    subst candidateIndex
    rw [lookup] at candidateLookup
    exact Option.some.inj candidateLookup.symm

end LeanTrominoes.StrictListRanks
