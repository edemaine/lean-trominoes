/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData

/-! # Exact values of descriptor occurrence-slot fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Counting slot tags on their own descriptor side recovers the semantic
slot index. -/
theorem slotValue_descriptorSlotUnits_same
    (side : RouteDescriptorPairFieldTags.Side)
    (descriptor : RouteDescriptor)
    (slot : DelimitedBinaryWordOccurrenceSlotTags.Slot) :
    slotValue (descriptorSlotUnits side (descriptor, slot)) side =
      slot.val := by
  rcases descriptor with ⟨vertexCount, edgeCount, edgeIndex,
    sourceVertexIndex, targetVertexIndex, sourcePortRank, targetPortRank,
    ⟨horizontal, vertical⟩⟩
  cases side <;>
    simp [slotValue, descriptorSlotUnits, descriptorSlotFields,
      taggedFields, RouteDescriptor.unaryFields, signedUnaryFields,
      nextField, List.count_replicate]

/-- Slot tags from the other descriptor side contribute nothing. -/
theorem slotValue_descriptorSlotUnits_other
    (descriptor : RouteDescriptor)
    (slot : DelimitedBinaryWordOccurrenceSlotTags.Slot) :
    slotValue (descriptorSlotUnits .second (descriptor, slot)) .first = 0 ∧
      slotValue (descriptorSlotUnits .first (descriptor, slot)) .second = 0 := by
  rcases descriptor with ⟨vertexCount, edgeCount, edgeIndex,
    sourceVertexIndex, targetVertexIndex, sourcePortRank, targetPortRank,
    ⟨horizontal, vertical⟩⟩
  simp [slotValue, descriptorSlotUnits, descriptorSlotFields,
    taggedFields, RouteDescriptor.unaryFields, signedUnaryFields,
    nextField, List.count_replicate]

/-- Counting slot tags in a complete canonical pair block recovers the slot
selected on either side. -/
@[simp] theorem slotValue_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor)
    (side : RouteDescriptorPairFieldTags.Side) :
    slotValue (descriptorSlotPairTokens pair) side =
      match side with
      | .first => pair.1.2.val
      | .second => pair.2.2.val := by
  rcases pair with ⟨⟨first, firstSlot⟩, ⟨second, secondSlot⟩⟩
  cases side with
  | first =>
      have same := slotValue_descriptorSlotUnits_same
        .first first firstSlot
      have other :=
        (slotValue_descriptorSlotUnits_other second secondSlot).1
      simp [slotValue, descriptorSlotPairTokens] at same other ⊢
      rw [same, other, Nat.add_zero]
  | second =>
      have same := slotValue_descriptorSlotUnits_same
        .second second secondSlot
      have other :=
        (slotValue_descriptorSlotUnits_other first firstSlot).2
      simp [slotValue, descriptorSlotPairTokens] at same other ⊢
      rw [other, same, Nat.zero_add]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
