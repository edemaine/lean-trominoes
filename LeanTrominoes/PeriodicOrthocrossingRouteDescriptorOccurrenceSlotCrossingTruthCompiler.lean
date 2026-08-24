/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthBooleanWordAnd
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingDescriptorTruthCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime

/-! # Batched truth compiler for slot-guarded affine crossings -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Descriptor and slot-guard truth words evaluated independently on the
same twelve-field pair block. -/
def componentTruthValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool × List Bool :=
  (descriptorTruthValues tokens,
    SlotGuardBatch.crossingTruthValues tokens)

/-- Pointwise conjunction of the aligned descriptor and slot-guard words. -/
def truthValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  FixedLengthBooleanWordAnd.output crossingSlots.length
    (componentTruthValues tokens)

/-- The complete slot-guarded crossing truth word is polynomial-time
computable without expanding the fixed predicate list into a fork tree. -/
noncomputable def truthValuesComputableInPolyTime :
    TM2ComputableInPolyTime id id truthValues := by
  let components := TM2ForkMachine.computableInPolyTime
    descriptorTruthValuesComputableInPolyTime
    SlotGuardBatch.crossingTruthValuesComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun tokens => FixedLengthBooleanWordAnd.output crossingSlots.length
      (componentTruthValues tokens))
  exact TM2CompositionMachine.computableInPolyTime components
    (FixedLengthBooleanWordAnd.outputComputableInPolyTime
      crossingSlots.length)

@[simp] theorem descriptorTruthValues_length
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (descriptorTruthValues tokens).length = crossingSlots.length := by
  rw [descriptorTruthValues_eq, List.length_map]

@[simp] theorem slotGuardTruthValues_length
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (SlotGuardBatch.crossingTruthValues tokens).length =
      crossingSlots.length := by
  unfold SlotGuardBatch.crossingTruthValues SlotGuardBatch.truthValues
    FiniteStateTransducer.output
  rw [SlotGuardBatch.scan_eq_addSlotValues]
  simp [SlotGuardBatch.finish]

/-- The compiled combination is the pointwise conjunction of its two aligned
component truth words. -/
theorem truthValues_eq_zipWith
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    truthValues tokens =
      List.zipWith (· && ·)
        (descriptorTruthValues tokens)
        (SlotGuardBatch.crossingTruthValues tokens) := by
  unfold truthValues componentTruthValues
  exact FixedLengthBooleanWordAnd.output_eq_zipWith
    crossingSlots.length
    (descriptorTruthValues tokens)
    (SlotGuardBatch.crossingTruthValues tokens)
    (descriptorTruthValues_length tokens)
    (slotGuardTruthValues_length tokens)

theorem zipWith_and_map_same
    (items : List α) (first second : α → Bool) :
    List.zipWith (· && ·) (items.map first) (items.map second) =
      items.map fun item => first item && second item := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, induction]

/-- On a canonical descriptor-slot pair, the compiled truth word is exactly
the semantic slot-guarded affine crossing activation word. -/
@[simp] theorem truthValues_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    truthValues (descriptorSlotPairTokens pair) =
      crossingActivations (descriptorSlotPairTokens pair) := by
  rw [truthValues_eq_zipWith, descriptorTruthValues_eq,
    SlotGuardBatch.crossingTruthValues_descriptorSlotPairTokens,
    zipWith_and_map_same]
  unfold crossingActivations
  apply List.map_congr_left
  intro slot _
  simp [Slot.evalTokens, slotValue_descriptorSlotPairTokens,
    Bool.and_assoc]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
