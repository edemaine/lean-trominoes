/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration
import LeanTrominoes.StableOccurrenceRanksGroupedIndices

/-! # Presentation indices in the source occurrence-entry order -/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

/-- Under the three-occurrence bound, used slots are exactly the increasing
ranks below the actual atom multiplicity, including the empty case. -/
theorem usedSlots_map_index_eq_range
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (countLe : source.variableOccurrences.count atom ≤ 3) :
    (usedSlots source atom).map (fun slot => slot.index) =
      List.range (source.variableOccurrences.count atom) := by
  rw [← PeriodicOneInThreeToThreeDM.occurrencesOf_length] at countLe ⊢
  unfold usedSlots occurrenceAt PeriodicOneInThreeToThreeDM.occurrenceAt
  generalize PeriodicOneInThreeToThreeDM.occurrencesOf source atom = occurrences at countLe ⊢
  cases occurrences with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      cases rest with
      | nil => rfl
      | cons third rest =>
        cases rest with
        | nil => rfl
        | cons fourth rest => simp only [List.length_cons] at countLe; omega

/-- The canonical source occurrence entries recover exactly the grouped
clause/literal presentation indices, with identical order. -/
theorem occurrenceEntries_map_index_eq_groupedIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (countLe : ∀ atom ∈ source.variableOccurrences,
      source.variableOccurrences.count atom ≤ 3) :
    (occurrenceEntries source).map (fun entry =>
      (source.variableOccurrences.idxsOf entry.1).getD entry.2.index 0) =
      StableOccurrenceRanks.groupedIndices source.variableOccurrences := by
  unfold occurrenceEntries occurringVariables PeriodicOneInThreeToThreeDM.occurringVariables
  rw [List.map_flatMap]
  unfold StableOccurrenceRanks.groupedIndices
  apply List.flatMap_congr
  intro atom member
  have countLe := countLe atom (List.mem_dedup.mp member)
  rw [List.map_map]
  change (usedSlots source atom).map
    ((fun index => (source.variableOccurrences.idxsOf atom).getD index 0) ∘
      (fun slot => slot.index)) = _
  rw [← List.map_map, usedSlots_map_index_eq_range source atom countLe]
  apply List.ext_getElem
  · simp
  · intro index firstLt secondLt
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ secondLt

/-- The clause/literal presentation index selected by one source entry. -/
def occurrenceEntryIndex {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (entry : Variable × OccurrenceSlot) : Nat :=
  (source.variableOccurrences.idxsOf entry.1).getD entry.2.index 0

/-- The selected presentation really has this entry's atom and stable rank.
No global occurrence bound is needed for an active entry. -/
theorem occurrenceEntryIndex_spec
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (entry : Variable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries source) :
    source.variableOccurrences[occurrenceEntryIndex source entry]? = some entry.1 ∧
      (StableOccurrenceRanks.ranks source.variableOccurrences).getD
        (occurrenceEntryIndex source entry) 0 = entry.2.index := by
  obtain ⟨tagged, lookup⟩ := occurrenceAt_exists_of_entry_mem source entry member
  have rankLt : entry.2.index < source.variableOccurrences.count entry.1 := by
    unfold occurrenceAt PeriodicOneInThreeToThreeDM.occurrenceAt at lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    simpa only [PeriodicOneInThreeToThreeDM.occurrencesOf_length] using bound
  have rankIndexLt : entry.2.index <
      (source.variableOccurrences.idxsOf entry.1).length := by simpa using rankLt
  have atomLookup : source.variableOccurrences[occurrenceEntryIndex source entry]? = some entry.1 := by
    unfold occurrenceEntryIndex
    rw [List.getD_eq_getElem _ _ rankIndexLt]
    have indexLt := List.getElem_idxsOf_lt rankIndexLt
    rw [List.getElem?_eq_getElem (by simpa using indexLt)]
    congr 1
    exact List.getElem_getElem_idxsOf_of_lawful rankIndexLt
  refine ⟨atomLookup, ?_⟩
  have rankLookup := StableOccurrenceRanks.ranks_getElem?
    source.variableOccurrences (occurrenceEntryIndex source entry)
  rw [atomLookup, Option.map_some] at rankLookup
  have countEq : (source.variableOccurrences.take
      (occurrenceEntryIndex source entry)).count entry.1 = entry.2.index := by
    unfold occurrenceEntryIndex
    rw [List.getD_eq_getElem _ _ rankIndexLt]
    exact StableOccurrenceRanks.count_take_getElem_idxsOf _ _ _ rankLt
  rw [countEq] at rankLookup
  simp only [List.getD_eq_getElem?_getD, rankLookup, Option.getD_some]

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
