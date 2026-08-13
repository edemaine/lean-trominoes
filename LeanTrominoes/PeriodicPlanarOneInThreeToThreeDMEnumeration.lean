/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMWellFormed
import LeanTrominoes.PeriodicOneInThreeToThreeDMNodup

/-!
# Enumeration facts for the planar periodic 3DM assembly

The global presentation groups occurrence modules first by source variable
and then by one of three used slots.  This file packages that nested order as
a duplicate-free list of `(variable, slot)` entries.  Later incidence proofs
can therefore localize a private element to exactly one finite gadget block.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Filtering the three distinct occurrence slots preserves distinctness. -/
theorem usedSlots_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (usedSlots source atom).Nodup := by
  exact (show allOccurrenceSlots.Nodup by decide).filter _

/-- Variable/slot pairs in the stable module enumeration order. -/
def occurrenceEntries {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Variable × OccurrenceSlot) :=
  (occurringVariables source).flatMap fun atom =>
    (usedSlots source atom).map fun slot => (atom, slot)

/-- Membership in the flattened enumeration is exactly nested membership in
the occurring-variable and used-slot lists. -/
theorem mem_occurrenceEntries_iff {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (atom, slot) ∈ occurrenceEntries source ↔
      atom ∈ occurringVariables source ∧
        slot ∈ usedSlots source atom := by
  simp [occurrenceEntries]

/-- The variable/slot module enumeration contains no duplicates. -/
theorem occurrenceEntries_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (occurrenceEntries source).Nodup := by
  rw [occurrenceEntries, List.nodup_flatMap]
  constructor
  · intro atom atomMember
    exact (usedSlots_nodup source atom).map fun
      firstSlot secondSlot equal => by
        cases equal
        rfl
  · exact
      (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source).imp
        fun {first second} different =>
          List.disjoint_left.mpr fun entry firstMember secondMember => by
            rcases List.mem_map.mp firstMember with
              ⟨firstSlot, firstSlotMember, rfl⟩
            rcases List.mem_map.mp secondMember with
              ⟨secondSlot, secondSlotMember, equal⟩
            exact different (Prod.mk.inj equal).1.symm

/-- The original nested variable-triple list is the flat-map of the packaged
module entries. -/
theorem variableTriples_eq_occurrenceEntries_flatMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    variableTriples source =
      (occurrenceEntries source).flatMap fun entry =>
        occurrenceTriples source entry.1 entry.2 := by
  unfold variableTriples occurrenceEntries
  induction occurringVariables source with
  | nil => rfl
  | cons atom rest induction =>
      simp only [List.flatMap_cons, induction]
      induction usedSlots source atom with
      | nil => rfl
      | cons slot slots slotInduction =>
          simp [slotInduction]

/-- Every occurrence entry contains an actual tagged source occurrence. -/
theorem occurrenceAt_exists_of_entry_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source) :
    ∃ tagged, occurrenceAt source entry.1 entry.2 = some tagged := by
  exact exists_occurrenceAt_of_mem_usedSlots
    source entry.1 entry.2
      ((mem_occurrenceEntries_iff
        source entry.1 entry.2).mp entryMember).2

/-- Every listed local occurrence block is duplicate-free. -/
theorem occurrenceTriples_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (occurrenceTriples source atom slot).Nodup := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples]

/-- Every listed local clause block is duplicate-free. -/
theorem clauseSetTriples_nodup {Variable : Type*}
    (clauseIndex : Nat) :
    (allClauseSets.map
      (Triple.clause (Variable := Variable) clauseIndex)).Nodup := by
  exact (show allClauseSets.Nodup by decide).map fun
    first second equal => by
      cases equal
      rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
