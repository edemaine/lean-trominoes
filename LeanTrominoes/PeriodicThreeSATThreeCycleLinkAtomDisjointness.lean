/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomCycleSemantics

/-! # Membership and disjointness of cycle endpoint words -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

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

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
