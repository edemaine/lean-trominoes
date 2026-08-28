/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingTruthCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingTruthListCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotGuardBatchSemantics
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotTags

/-! # Semantics of arbitrary fixed crossing-slot truth lists -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

@[simp] theorem descriptorTruthValuesFor_eq
    (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    descriptorTruthValuesFor slots tokens =
      slots.map fun slot =>
        slot.descriptorPredicate.evalTokens (descriptorTokens tokens) := by
  unfold descriptorTruthValuesFor
  rw [predicateListTruthValues_eq, List.map_map]
  rfl

@[simp] theorem descriptorTruthValuesFor_length
    (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (descriptorTruthValuesFor slots tokens).length = slots.length := by
  rw [descriptorTruthValuesFor_eq, List.length_map]

@[simp] theorem slotGuardTruthValuesFor_length
    (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    (SlotGuardBatch.truthValues slots tokens).length = slots.length := by
  unfold SlotGuardBatch.truthValues FiniteStateTransducer.output
  rw [SlotGuardBatch.scan_eq_addSlotValues]
  simp [SlotGuardBatch.finish]

theorem truthValuesFor_eq_zipWith
    (slots : List Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    truthValuesFor slots tokens =
      List.zipWith (· && ·)
        (descriptorTruthValuesFor slots tokens)
        (SlotGuardBatch.truthValues slots tokens) := by
  unfold truthValuesFor componentTruthValuesFor
  exact FixedLengthBooleanWordAnd.output_eq_zipWith slots.length
    (descriptorTruthValuesFor slots tokens)
    (SlotGuardBatch.truthValues slots tokens)
    (descriptorTruthValuesFor_length slots tokens)
    (slotGuardTruthValuesFor_length slots tokens)

/-- On a canonical descriptor-slot pair, the generic compiled truth word is
exactly pointwise evaluation of the supplied fixed slots. -/
@[simp] theorem truthValuesFor_descriptorSlotPairTokens
    (slots : List Slot) (pair : TaggedDescriptor × TaggedDescriptor) :
    truthValuesFor slots (descriptorSlotPairTokens pair) =
      slots.map fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair) := by
  rw [truthValuesFor_eq_zipWith, descriptorTruthValuesFor_eq,
    SlotGuardBatch.truthValues_descriptorSlotPairTokens,
    zipWith_and_map_same]
  apply List.map_congr_left
  intro slot _slotMember
  simp [Slot.evalTokens, slotValue_descriptorSlotPairTokens,
    Bool.and_assoc]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
