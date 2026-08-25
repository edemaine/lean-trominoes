/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical indexed crossing-segment field streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingIndexedSegmentFieldStream

open CarrierCrossingIndexedSegmentField
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem emittedFields_encodeDescriptorSlotPairs
    (field : Field) (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedFields field
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingIndexedSegmentFields
            field
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold emittedFields
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end CrossingIndexedSegmentFieldStream
end LeanTrominoes.PeriodicOrthocrossing
