/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupPortRankWord
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkTargetIndexSemantics

/-! # Port-rank words of grouped occurrence cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

theorem linkAtoms_append
    {Value : Type*} (first second : List (Value × Value)) :
    linkAtoms (first ++ second) =
      linkAtoms first ++ linkAtoms second := by
  induction first with
  | nil => rfl
  | cons link first induction =>
      simp only [List.cons_append, linkAtoms]
      rw [induction]

theorem linkAtoms_groupedLinks
    {Variable : Type*}
    (groups : List (List (ThreeOccurrenceVariable Variable))) :
    linkAtoms (CycleLinkGroupedTargetIndices.groupedLinks groups) =
      groups.flatMap cycleLinkAtoms := by
  induction groups with
  | nil => rfl
  | cons group groups induction =>
      simp only [CycleLinkGroupedTargetIndices.groupedLinks,
        List.flatMap_cons, linkAtoms_append, cycleLinkAtoms]
      change linkAtoms (List.flatMap cycleLinks groups) =
        List.flatMap cycleLinkAtoms groups at induction
      rw [induction]

@[simp] theorem mem_cycleLinkAtoms_iff
    {Variable : Type*}
    (value : ThreeOccurrenceVariable Variable)
    (values : List (ThreeOccurrenceVariable Variable)) :
    value ∈ cycleLinkAtoms values ↔ value ∈ values := by
  cases values with
  | nil => rfl
  | cons first rest =>
      rw [cycleLinkAtoms_cons]
      simp
      tauto

theorem cycleLinkAtoms_disjoint
    {Variable : Type*}
    (first second : List (ThreeOccurrenceVariable Variable))
    (disjoint : List.Disjoint first second) :
    List.Disjoint (cycleLinkAtoms first) (cycleLinkAtoms second) := by
  rw [List.disjoint_left]
  intro value firstMember secondMember
  exact (List.disjoint_left.mp disjoint)
    ((mem_cycleLinkAtoms_iff value first).mp firstMember)
    ((mem_cycleLinkAtoms_iff value second).mp secondMember)

theorem cycleLinkAtoms_disjoint_flatMap
    {Variable : Type*}
    (group : List (ThreeOccurrenceVariable Variable))
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (disjoint : List.Disjoint group groups.flatten) :
    List.Disjoint (cycleLinkAtoms group)
      (groups.flatMap cycleLinkAtoms) := by
  rw [List.disjoint_left]
  intro value groupMember groupsMember
  have valueInGroup :=
    (mem_cycleLinkAtoms_iff value group).mp groupMember
  rw [List.mem_flatMap] at groupsMember
  obtain ⟨tailGroup, tailGroupMember, valueMember⟩ := groupsMember
  have valueInTail : value ∈ groups.flatten := by
    rw [List.mem_flatten]
    exact ⟨tailGroup, tailGroupMember,
      (mem_cycleLinkAtoms_iff value tailGroup).mp valueMember⟩
  exact (List.disjoint_left.mp disjoint) valueInGroup valueInTail

theorem prefixRanks_groupedCycleLinkAtoms
    {Variable : Type*} [DecidableEq Variable]
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (nodup : groups.flatten.Nodup) :
    prefixRanks (groups.flatMap cycleLinkAtoms) =
      groups.flatMap fun group => groupRankWord group.length := by
  induction groups with
  | nil => rfl
  | cons group groups induction =>
      have appendNodup : (group ++ groups.flatten).Nodup := by
        simpa using nodup
      have parts := List.nodup_append.mp appendNodup
      have disjoint : List.Disjoint group groups.flatten := by
        rw [List.disjoint_left]
        intro value groupMember tailMember
        exact parts.2.2 value groupMember value tailMember rfl
      have atomsDisjoint := cycleLinkAtoms_disjoint_flatMap
        group groups disjoint
      rw [List.flatMap_cons,
        prefixRanks_append_of_disjoint _ _ atomsDisjoint,
        prefixRanks_cycleLinkAtoms group parts.1,
        induction parts.2.1]
      rfl

/-- The global endpoint-prefix ranks are the closed rank word of each source
variable's occurrence group, in source-variable order. -/
theorem allCycleLinks_prefixRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    prefixRanks (linkAtoms (allCycleLinks source)) =
      (sourceVariables source).flatMap fun atom =>
        groupRankWord (occurrenceVariables source atom).length := by
  have grouped := prefixRanks_groupedCycleLinkAtoms
    (CycleLinkGroupedTargetIndices.occurrenceGroups source)
    (CycleLinkGroupedTargetIndices.occurrenceGroups_flatten_nodup source)
  rw [← linkAtoms_groupedLinks,
    CycleLinkGroupedTargetIndices.occurrenceGroups_groupedLinks] at grouped
  simpa [CycleLinkGroupedTargetIndices.occurrenceGroups,
    List.flatMap_map] using grouped

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
