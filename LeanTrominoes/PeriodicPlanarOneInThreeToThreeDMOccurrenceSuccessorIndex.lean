/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntryIndices
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSoundness

/-! # The actual occurrence successor is modular rank succession -/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

/-- The geometric assembly's next used slot increments the current rank
modulo its active slot count, including a one-occurrence cycle. -/
theorem nextUsedSlot_index_eq_mod_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    (nextUsedSlot source atom slot).index =
      (slot.index + 1) % (usedSlots source atom).length := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with one | two | three
  all_goals
    cases slot <;>
      simp_all [nextUsedSlot, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index]

/-- Under the reduction's occurrence bound, the same modulus is the actual
source multiplicity used by the numeric cyclic-key compiler. -/
theorem nextUsedSlot_index_eq_mod_count
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (countLe : source.variableOccurrences.count atom ≤ 3) :
    (nextUsedSlot source atom slot).index =
      (slot.index + 1) % source.variableOccurrences.count atom := by
  have lengthEq := congrArg List.length (usedSlots_map_index_eq_range source atom countLe)
  simp only [List.length_map, List.length_range] at lengthEq
  rw [← lengthEq]
  exact nextUsedSlot_index_eq_mod_length source atom atomMember slot slotMember

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
