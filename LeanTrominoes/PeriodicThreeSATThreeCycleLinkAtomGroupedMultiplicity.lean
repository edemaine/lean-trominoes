/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomCycleMultiplicity
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomDisjointness

/-! # Endpoint multiplicity across disjoint occurrence cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- Concatenating endpoint words from disjoint duplicate-free groups leaves
every presented endpoint with multiplicity two. -/
theorem groupedCycleLinkAtoms_count_eq_two
    {Variable : Type*} [DecidableEq Variable]
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (groupsNodup : groups.flatten.Nodup) :
    ∀ value ∈ groups.flatMap cycleLinkAtoms,
      (groups.flatMap cycleLinkAtoms).count value = 2 := by
  induction groups with
  | nil => simp
  | cons group groups induction =>
      have appendNodup : (group ++ groups.flatten).Nodup := by
        simpa using groupsNodup
      have parts := List.nodup_append.mp appendNodup
      have groupNodup := parts.1
      have groupsNodup' := parts.2.1
      have disjoint : List.Disjoint group groups.flatten := by
        rw [List.disjoint_left]
        intro value groupMember tailMember
        exact parts.2.2 value groupMember value tailMember rfl
      have atomsDisjoint :=
        cycleLinkAtoms_disjoint_flatMap group groups disjoint
      intro value valueMember
      rw [List.flatMap_cons] at valueMember ⊢
      rcases List.mem_append.mp valueMember with
        headMember | tailMember
      · have tailAbsent : value ∉ groups.flatMap cycleLinkAtoms := by
          intro valueTailMember
          exact (List.disjoint_left.mp atomsDisjoint)
            headMember valueTailMember
        rw [List.count_append,
          cycleLinkAtoms_count_eq_two_of_mem
            group groupNodup value headMember,
          List.count_eq_zero.mpr tailAbsent, Nat.add_zero]
      · have headAbsent : value ∉ cycleLinkAtoms group := by
          intro valueHeadMember
          exact (List.disjoint_left.mp atomsDisjoint)
            valueHeadMember tailMember
        rw [List.count_append, List.count_eq_zero.mpr headAbsent,
          Nat.zero_add]
        exact induction groupsNodup' value tailMember

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
