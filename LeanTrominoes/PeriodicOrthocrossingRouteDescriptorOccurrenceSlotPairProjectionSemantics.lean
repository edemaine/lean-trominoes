/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics

/-! # Descriptor projection from twelve-field occurrence-slot pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem descriptorTokens_replicate_descriptorUnit
    (side : Side) (field : Fin 12) (number : Nat)
    (within : field.val < 11) :
    (List.replicate number (.unit side field)).flatMap
        descriptorProjection =
      List.replicate number
        (.unit side ⟨field.val, within⟩ :
          RouteDescriptorPairFieldTags.Token) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ,
        List.flatMap_cons]
      simp [descriptorProjection, within, induction]

@[simp] theorem descriptorTokens_replicate_slotUnit
    (side : Side) (number : Nat) :
    (List.replicate number (.unit side (11 : Fin 12))).flatMap
        descriptorProjection = [] := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.flatMap_cons]
      simp [descriptorProjection, induction]

/-- Deleting slot-field units from one canonical tagged descriptor leaves
exactly the existing eleven-field tagged descriptor units. -/
theorem descriptorTokens_descriptorSlotUnits
    (side : Side) (descriptor : RouteDescriptor)
    (slot : DelimitedBinaryWordOccurrenceSlotTags.Slot) :
    (descriptorSlotUnits side (descriptor, slot)).flatMap
        descriptorProjection =
      RouteDescriptorPairFieldTags.descriptorUnits side descriptor := by
  rcases descriptor with ⟨vertexCount, edgeCount, edgeIndex,
    sourceVertexIndex, targetVertexIndex, sourcePortRank, targetPortRank,
    ⟨horizontal, vertical⟩⟩
  cases side <;>
    simp [descriptorSlotUnits, descriptorSlotFields, taggedFields,
      RouteDescriptorPairFieldTags.descriptorUnits,
      RouteDescriptorPairFieldTags.taggedFields,
      RouteDescriptor.unaryFields, signedUnaryFields, nextField,
      RouteDescriptorPairFieldTags.nextField]

/-- Descriptor projection of one canonical twelve-field pair block is the
canonical existing eleven-field pair block for the underlying descriptors. -/
@[simp] theorem descriptorTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    descriptorTokens (descriptorSlotPairTokens pair) =
      RouteDescriptorPairFieldTags.descriptorPairTokens
        (pair.1.1, pair.2.1) := by
  rcases pair with ⟨⟨first, firstSlot⟩, ⟨second, secondSlot⟩⟩
  unfold descriptorTokens descriptorSlotPairTokens
    RouteDescriptorPairFieldTags.descriptorPairTokens
  simp [descriptorProjection,
    descriptorTokens_descriptorSlotUnits]

/-- Projecting a canonical slot-pair stream preserves pair order and removes
only the occurrence-slot fields. -/
theorem descriptorTokens_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    descriptorTokens (encodeDescriptorSlotPairs pairs) =
      pairs.flatMap fun pair =>
        RouteDescriptorPairFieldTags.descriptorPairTokens
          (pair.1.1, pair.2.1) := by
  unfold descriptorTokens encodeDescriptorSlotPairs
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair _
  exact descriptorTokens_descriptorSlotPairTokens pair

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
