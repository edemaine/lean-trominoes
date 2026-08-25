/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical ownership-shift field streams -/

namespace LeanTrominoes.PeriodicOrthocrossing

namespace TerminalOwnershipShiftFieldStream

open CarrierOwnershipShiftField

@[simp] theorem emittedFields_encodeDescriptorPairs
    (field : Field)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedFields field
        (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorPairAffine.terminalOwnershipShiftFields field
            (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) := by
  unfold emittedFields
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end TerminalOwnershipShiftFieldStream

namespace CrossingOwnershipShiftFieldStream

open CarrierOwnershipShiftField
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem emittedFields_encodeDescriptorSlotPairs
    (field : Field)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedFields field
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftFields
            field
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold emittedFields
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end CrossingOwnershipShiftFieldStream
end LeanTrominoes.PeriodicOrthocrossing
