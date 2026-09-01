/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceSlotCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCountPredCompiler
import LeanTrominoes.StableOccurrenceRanksBounds

/-! # Active finite slots from stable occurrence ranks -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {Value : Type*} [DecidableEq Value]

private theorem active_of_valid :
    ∀ {ranks sizes : List Nat},
      UnarySuccessorEqualityFilterMachine.Valid ranks sizes →
      (∀ size ∈ sizes, size ≤ 3) →
      List.Forall₂
        (fun slot countPred => slot.index < countPred.val + 1)
        (ranks.map BoundedOccurrenceSlots.boundedOccurrenceSlot)
        (sizes.map BoundedPositiveCountPreds.boundedPositiveCountPred)
  | [], [], .nil, _ => List.Forall₂.nil
  | rank :: ranks, size :: sizes, .cons rankLt rest, atMostThree => by
      apply List.Forall₂.cons
      · have sizeLe : size ≤ 3 := atMostThree size (by simp)
        rw [BoundedOccurrenceSlots.boundedOccurrenceSlot_index_of_lt_three
            rank (lt_of_lt_of_le rankLt sizeLe),
          BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
            size (by omega) sizeLe]
        exact rankLt
      · exact active_of_valid rest fun other otherMember =>
          atMostThree other (by simp [otherMember])

/-- If no value occurs more than three times, every stable zero-based rank
selects an active slot of the finite fan whose predecessor encodes that
value's multiplicity. -/
theorem slots_countPreds_active_of_count_le_three
    (values : List Value)
    (countLe : ∀ value ∈ values, values.count value ≤ 3) :
    List.Forall₂
      (fun slot countPred => slot.index < countPred.val + 1)
      (BoundedOccurrenceSlots.slots (ranks values))
      (values.map fun value =>
        BoundedPositiveCountPreds.boundedPositiveCountPred
          (values.count value)) := by
  unfold BoundedOccurrenceSlots.slots
  have valid := ranks_valid values
  have active := active_of_valid valid (fun size sizeMember => by
    rcases List.mem_map.mp sizeMember with ⟨value, valueMember, rfl⟩
    exact countLe value valueMember)
  change List.Forall₂ _ _
    (List.map
      (BoundedPositiveCountPreds.boundedPositiveCountPred ∘
        fun value => values.count value) values)
  simpa only [List.map_map] using active

end LeanTrominoes.StableOccurrenceRanks
