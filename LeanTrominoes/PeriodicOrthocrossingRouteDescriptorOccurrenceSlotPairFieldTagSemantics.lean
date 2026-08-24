/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerFunctionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTags

/-! # Exact semantics of twelve-field descriptor occurrence-slot tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem transition_sideBit_false
    (side : Side) (field : Fin 12) :
    transition (sideControl side field) (sideBit side false) =
      (sideControl side field, [.unit side field]) := by
  cases side <;> rfl

@[simp] theorem transition_sideBit_true
    (side : Side) (field : Fin 12) :
    transition (sideControl side field) (sideBit side true) =
      (sideControl side (nextField field), []) := by
  cases side <;> rfl

theorem scan_units (side : Side) (field : Fin 12) (number : Nat) :
    LightweightFiniteStateTransducer.scan transition (sideControl side field)
        (List.replicate number (sideBit side false)) =
      (sideControl side field,
        List.replicate number (.unit side field)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [LightweightFiniteStateTransducer.scan,
        transition_sideBit_false]
      rw [induction]
      rfl

theorem scan_fieldWord
    (side : Side) (field : Fin 12) (number : Nat) :
    LightweightFiniteStateTransducer.scan transition (sideControl side field)
        ((RouteDescriptorBinaryWords.fieldWord number).map
          (sideBit side)) =
      (sideControl side (nextField field),
        List.replicate number (.unit side field)) := by
  rw [show (RouteDescriptorBinaryWords.fieldWord number).map
      (sideBit side) =
        List.replicate number (sideBit side false) ++
          [sideBit side true] by
    simp [RouteDescriptorBinaryWords.fieldWord]]
  rw [LightweightFiniteStateTransducer.scan_append, scan_units]
  dsimp
  simp only [LightweightFiniteStateTransducer.scan,
    transition_sideBit_true,
    List.append_nil]

theorem scan_fields
    (side : Side) (field : Fin 12) (numbers : List Nat) :
    LightweightFiniteStateTransducer.scan transition (sideControl side field)
        ((numbers.flatMap
          RouteDescriptorBinaryWords.fieldWord).map (sideBit side)) =
      (sideControl side (advanceFields field numbers.length),
        taggedFields side field numbers) := by
  induction numbers generalizing field with
  | nil => rfl
  | cons number numbers induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [LightweightFiniteStateTransducer.scan_append, scan_fieldWord]
      dsimp
      rw [induction]
      rfl

theorem descriptorSlotWord_eq_fields
    (tagged : TaggedDescriptor) :
    descriptorSlotWord tagged =
      (descriptorSlotFields tagged).flatMap
        RouteDescriptorBinaryWords.fieldWord := by
  rcases tagged with ⟨descriptor, slot⟩
  simp [descriptorSlotWord,
    DelimitedBinaryWordOccurrenceSlotTags.slotWord,
    RouteDescriptorBinaryWords.descriptorWord,
    descriptorSlotFields, RouteDescriptorBinaryWords.fieldWord,
    List.append_assoc]

theorem scan_descriptorSlotWord
    (side : Side) (tagged : TaggedDescriptor) :
    LightweightFiniteStateTransducer.scan transition (sideControl side 0)
        ((descriptorSlotWord tagged).map (sideBit side)) =
      (sideControl side 0, descriptorSlotUnits side tagged) := by
  rw [descriptorSlotWord_eq_fields, scan_fields]
  have fieldsLength : (descriptorSlotFields tagged).length = 12 := by
    simp [descriptorSlotFields, RouteDescriptor.unaryFields,
      signedUnaryFields]
  rw [fieldsLength]
  rfl

theorem scan_firstDescriptorSlotWord (tagged : TaggedDescriptor) :
    LightweightFiniteStateTransducer.scan transition (.first 0)
        ((descriptorSlotWord tagged).map
          DelimitedBinaryWordPairs.Token.firstBit) =
      (.first 0, descriptorSlotUnits .first tagged) := by
  change LightweightFiniteStateTransducer.scan transition
      (sideControl RouteDescriptorPairFieldTags.Side.first 0)
      ((descriptorSlotWord tagged).map
        (sideBit RouteDescriptorPairFieldTags.Side.first)) = _
  exact scan_descriptorSlotWord
    RouteDescriptorPairFieldTags.Side.first tagged

theorem scan_secondDescriptorSlotWord (tagged : TaggedDescriptor) :
    LightweightFiniteStateTransducer.scan transition (.second 0)
        ((descriptorSlotWord tagged).map
          DelimitedBinaryWordPairs.Token.secondBit) =
      (.second 0, descriptorSlotUnits .second tagged) := by
  change LightweightFiniteStateTransducer.scan transition
      (sideControl RouteDescriptorPairFieldTags.Side.second 0)
      ((descriptorSlotWord tagged).map
        (sideBit RouteDescriptorPairFieldTags.Side.second)) = _
  exact scan_descriptorSlotWord
    RouteDescriptorPairFieldTags.Side.second tagged

theorem scan_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    LightweightFiniteStateTransducer.scan transition .between
        (DelimitedBinaryWordPairs.pairTokens
          (descriptorSlotWord pair.1, descriptorSlotWord pair.2)) =
      (.between, descriptorSlotPairTokens pair) := by
  rcases pair with ⟨first, second⟩
  unfold DelimitedBinaryWordPairs.pairTokens descriptorSlotPairTokens
  simp only [LightweightFiniteStateTransducer.scan, transition]
  dsimp
  rw [LightweightFiniteStateTransducer.scan_append,
    scan_firstDescriptorSlotWord first]
  dsimp
  simp only [LightweightFiniteStateTransducer.scan, transition]
  dsimp
  rw [LightweightFiniteStateTransducer.scan_append,
    scan_secondDescriptorSlotWord second]
  dsimp
  simp only [LightweightFiniteStateTransducer.scan, transition,
    List.append_assoc,
    List.append_nil]

theorem scan_descriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    LightweightFiniteStateTransducer.scan transition .between
        (pairs.flatMap fun pair =>
          DelimitedBinaryWordPairs.pairTokens
            (descriptorSlotWord pair.1, descriptorSlotWord pair.2)) =
      (.between, encodeDescriptorSlotPairs pairs) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, LightweightFiniteStateTransducer.scan_append,
        scan_descriptorSlotPairTokens]
      dsimp
      rw [induction]
      rfl

/-- Tagging the canonical slot-word pair encoding yields exactly the
twelve-field stream indexed by the tagged-descriptor square. -/
theorem tokens_wordPairs (descriptors : List RouteDescriptor) :
    tokens (DelimitedBinaryWordPairs.encode (wordPairs descriptors)) =
      encodeDescriptorSlotPairs
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors) := by
  unfold tokens LightweightFiniteStateTransducer.output
    DelimitedBinaryWordPairs.encode wordPairs
  rw [List.flatMap_map, scan_descriptorSlotPairs]
  simp only [finish, List.append_nil]

@[simp] theorem inputTokens_wordPairs
    (descriptors : List RouteDescriptor) :
    inputTokens (wordPairs descriptors) =
      encodeDescriptorSlotPairs
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors) := by
  exact tokens_wordPairs descriptors

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
