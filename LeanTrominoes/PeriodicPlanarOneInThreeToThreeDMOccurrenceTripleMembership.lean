/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration

/-! # Ownership and global membership of occurrence triples -/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

/-- Every local triple retains the variable and occurrence slot of its block. -/
theorem occurrenceTriples_member_cases
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) (slot : OccurrenceSlot)
    (triple : Triple Variable) (member : triple ∈ occurrenceTriples source atom slot) :
    (∃ variant localTriple, triple = Triple.ordinary atom slot variant localTriple) ∨
      (∃ localTriple, triple = Triple.fixedRed atom slot localTriple) := by
  cases kind : occurrenceConnectorKind source atom slot with
  | fixedRed =>
      rw [occurrenceTriples, kind] at member
      obtain ⟨localTriple, _localMember, rfl⟩ := List.mem_map.mp member
      exact .inr ⟨localTriple, rfl⟩
  | fixedGreen =>
      rw [occurrenceTriples, kind] at member
      obtain ⟨localTriple, _localMember, rfl⟩ := List.mem_map.mp member
      exact .inl ⟨.fixedGreen, localTriple, rfl⟩
  | fixedBlue =>
      rw [occurrenceTriples, kind] at member
      obtain ⟨localTriple, _localMember, rfl⟩ := List.mem_map.mp member
      exact .inl ⟨.fixedBlue, localTriple, rfl⟩

/-- A triple of an active occurrence entry belongs to the complete presentation. -/
theorem mem_triples_of_mem_occurrenceTriples
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source entry.1 entry.2) :
    triple ∈ triples source := by
  rw [triples, List.mem_append]
  left
  rw [variableTriples_eq_occurrenceEntries_flatMap]
  exact List.mem_flatMap.mpr ⟨entry, entryMember, tripleMember⟩

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
