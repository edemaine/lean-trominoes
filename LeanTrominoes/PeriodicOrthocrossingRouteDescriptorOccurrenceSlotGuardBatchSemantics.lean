/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchData

/-! # Exact semantics of batched occurrence-slot guards -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing
namespace SlotGuardBatch

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Add the two semantic slot-field counts to an arbitrary finite control. -/
def addSlotValues (control : Control)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    Control :=
  ⟨addCount control.first (slotValue tokens .first),
    addCount control.second (slotValue tokens .second)⟩

theorem addCount_add (count : Count) (first second : Nat) :
    addCount (addCount count first) second =
      addCount count (first + second) := by
  apply Fin.ext
  simp only [addCount]
  omega

@[simp] theorem addCount_zero (count : Count) :
    addCount count 0 = count := by
  apply Fin.ext
  change min (count.val + 0) 81 = count.val
  have bound := count.isLt
  omega

/-- The finite scan records exactly the two saturated twelfth-field counts
and emits nothing before its terminal action. -/
theorem scan_eq_addSlotValues
    (control : Control)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    FiniteStateTransducer.scan transition control tokens =
      (addSlotValues control tokens, []) := by
  induction tokens generalizing control with
  | nil =>
      rcases control with ⟨first, second⟩
      change (({ first := first, second := second } : Control), []) =
        (({ first := addCount first 0,
            second := addCount second 0 } : Control), [])
      rw [addCount_zero, addCount_zero]
  | cons token tokens induction =>
      cases token with
      | pairStart =>
          simp [FiniteStateTransducer.scan, transition, addSlotValues,
            slotValue, induction]
      | pairEnd =>
          simp [FiniteStateTransducer.scan, transition, addSlotValues,
            slotValue, induction]
      | unit side field =>
          cases side with
          | first =>
              by_cases selected : field = (11 : Fin 12)
              · subst field
                simp [FiniteStateTransducer.scan, transition, addSlotValues,
                  slotValue, induction, addCount_add, Nat.add_comm]
              · have fieldNe : field.val ≠ 11 := by
                  intro equal
                  exact selected (Fin.ext equal)
                simp [FiniteStateTransducer.scan, transition, addSlotValues,
                  slotValue, induction, selected, fieldNe]
          | second =>
              by_cases selected : field = (11 : Fin 12)
              · subst field
                simp [FiniteStateTransducer.scan, transition, addSlotValues,
                  slotValue, induction, addCount_add, Nat.add_comm]
              · have fieldNe : field.val ≠ 11 := by
                  intro equal
                  exact selected (Fin.ext equal)
                simp [FiniteStateTransducer.scan, transition, addSlotValues,
                  slotValue, induction, selected, fieldNe]

/-- On a canonical descriptor-slot pair, the batch evaluator emits exactly
one equality bit for every requested fixed slot pair. -/
theorem truthValues_descriptorSlotPairTokens
    (slots : List Slot)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    truthValues slots (descriptorSlotPairTokens pair) =
      slots.map fun slot =>
        decide (pair.1.2.val = slot.firstSlot) &&
          decide (pair.2.2.val = slot.secondSlot) := by
  unfold truthValues FiniteStateTransducer.output
  rw [scan_eq_addSlotValues]
  simp only [List.nil_append, addSlotValues]
  rw [slotValue_descriptorSlotPairTokens,
    slotValue_descriptorSlotPairTokens]
  unfold finish addCount
  have firstLe : pair.1.2.val ≤ 81 := by omega
  have secondLe : pair.2.2.val ≤ 81 := by omega
  simp [initial, firstLe, secondLe]

@[simp] theorem crossingTruthValues_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingTruthValues (descriptorSlotPairTokens pair) =
      crossingSlots.map fun slot =>
        decide (pair.1.2.val = slot.firstSlot) &&
          decide (pair.2.2.val = slot.secondSlot) := by
  exact truthValues_descriptorSlotPairTokens crossingSlots pair

end SlotGuardBatch
end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
