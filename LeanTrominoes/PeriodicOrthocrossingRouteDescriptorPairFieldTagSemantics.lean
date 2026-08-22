/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTags

/-! # Exact semantics of route-descriptor pair field tags -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

@[simp] theorem transition_sideBit_false
    (side : Side) (field : Fin 11) :
    transition (sideControl side field) (sideBit side false) =
      (sideControl side field, [.unit side field]) := by
  cases side <;> rfl

@[simp] theorem transition_sideBit_true
    (side : Side) (field : Fin 11) :
    transition (sideControl side field) (sideBit side true) =
      (sideControl side (nextField field), []) := by
  cases side <;> rfl

theorem scan_units (side : Side) (field : Fin 11) (number : Nat) :
    FiniteStateTransducer.scan transition (sideControl side field)
        (List.replicate number (sideBit side false)) =
      (sideControl side field,
        List.replicate number (.unit side field)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition_sideBit_false]
      rw [induction]
      rfl

theorem scan_fieldWord
    (side : Side) (field : Fin 11) (number : Nat) :
    FiniteStateTransducer.scan transition (sideControl side field)
        ((RouteDescriptorBinaryWords.fieldWord number).map
          (sideBit side)) =
      (sideControl side (nextField field),
        List.replicate number (.unit side field)) := by
  rw [show (RouteDescriptorBinaryWords.fieldWord number).map
      (sideBit side) =
        List.replicate number (sideBit side false) ++
          [sideBit side true] by
    simp [RouteDescriptorBinaryWords.fieldWord]]
  rw [FiniteStateTransducer.scan_append, scan_units]
  dsimp
  simp only [FiniteStateTransducer.scan, transition_sideBit_true,
    List.append_nil]

theorem scan_fields
    (side : Side) (field : Fin 11) (numbers : List Nat) :
    FiniteStateTransducer.scan transition (sideControl side field)
        ((numbers.flatMap
          RouteDescriptorBinaryWords.fieldWord).map (sideBit side)) =
      (sideControl side (advanceFields field numbers.length),
        taggedFields side field numbers) := by
  induction numbers generalizing field with
  | nil => rfl
  | cons number numbers induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [FiniteStateTransducer.scan_append, scan_fieldWord]
      dsimp
      rw [induction]
      rfl

theorem scan_descriptorWord
    (side : Side) (descriptor : RouteDescriptor) :
    FiniteStateTransducer.scan transition (sideControl side 0)
        ((RouteDescriptorBinaryWords.descriptorWord descriptor).map
          (sideBit side)) =
      (sideControl side 0, descriptorUnits side descriptor) := by
  unfold RouteDescriptorBinaryWords.descriptorWord descriptorUnits
  rw [scan_fields]
  have fieldsLength : descriptor.unaryFields.length = 11 := by
    simp [RouteDescriptor.unaryFields, signedUnaryFields]
  rw [fieldsLength]
  rfl

theorem scan_firstDescriptorWord (descriptor : RouteDescriptor) :
    FiniteStateTransducer.scan transition (.first 0)
        ((RouteDescriptorBinaryWords.descriptorWord descriptor).map
          DelimitedBinaryWordPairs.Token.firstBit) =
      (.first 0, descriptorUnits .first descriptor) := by
  change FiniteStateTransducer.scan transition
      (sideControl Side.first 0)
      ((RouteDescriptorBinaryWords.descriptorWord descriptor).map
        (sideBit Side.first)) = _
  exact scan_descriptorWord Side.first descriptor

theorem scan_secondDescriptorWord (descriptor : RouteDescriptor) :
    FiniteStateTransducer.scan transition (.second 0)
        ((RouteDescriptorBinaryWords.descriptorWord descriptor).map
          DelimitedBinaryWordPairs.Token.secondBit) =
      (.second 0, descriptorUnits .second descriptor) := by
  change FiniteStateTransducer.scan transition
      (sideControl Side.second 0)
      ((RouteDescriptorBinaryWords.descriptorWord descriptor).map
        (sideBit Side.second)) = _
  exact scan_descriptorWord Side.second descriptor

theorem scan_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    FiniteStateTransducer.scan transition .between
        (DelimitedBinaryWordPairs.pairTokens
          (RouteDescriptorBinaryWords.descriptorWord pair.1,
            RouteDescriptorBinaryWords.descriptorWord pair.2)) =
      (.between, descriptorPairTokens pair) := by
  rcases pair with ⟨first, second⟩
  unfold DelimitedBinaryWordPairs.pairTokens descriptorPairTokens
  simp only [FiniteStateTransducer.scan, transition]
  dsimp
  rw [FiniteStateTransducer.scan_append,
    scan_firstDescriptorWord first]
  dsimp
  simp only [FiniteStateTransducer.scan, transition]
  dsimp
  rw [FiniteStateTransducer.scan_append,
    scan_secondDescriptorWord second]
  dsimp
  simp only [FiniteStateTransducer.scan, transition, List.append_assoc,
    List.append_nil]

theorem scan_descriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    FiniteStateTransducer.scan transition .between
        (pairs.flatMap fun pair =>
          DelimitedBinaryWordPairs.pairTokens
            (RouteDescriptorBinaryWords.descriptorWord pair.1,
              RouteDescriptorBinaryWords.descriptorWord pair.2)) =
      (.between, encodeDescriptorPairs pairs) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, FiniteStateTransducer.scan_append,
        scan_descriptorPairTokens]
      dsimp
      rw [induction]
      rfl

/-- Tagging the canonical descriptor-word pair encoding produces exactly one
pair-delimited stream of side-and-field-tagged unary units. -/
theorem tokens_descriptorWordPairs
    (descriptors : List RouteDescriptor) :
    tokens
        (DelimitedBinaryWordPairs.encode
          (RouteDescriptorBinaryWordPairs.descriptorWordPairs
            descriptors)) =
      encodeDescriptorPairs (descriptors ×ˢ descriptors) := by
  unfold tokens FiniteStateTransducer.output
    DelimitedBinaryWordPairs.encode
    RouteDescriptorBinaryWordPairs.descriptorWordPairs
  rw [List.flatMap_map]
  rw [scan_descriptorPairs]
  simp only [finish, List.append_nil]

@[simp] theorem inputTokens_descriptorWordPairs
    (descriptors : List RouteDescriptor) :
    inputTokens
        (RouteDescriptorBinaryWordPairs.descriptorWordPairs descriptors) =
      encodeDescriptorPairs (descriptors ×ˢ descriptors) := by
  exact tokens_descriptorWordPairs descriptors

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
