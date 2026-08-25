/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical semantics of crossing-point field streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingPointFieldStream

open CarrierCrossingPointField
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem emittedFields_encodeDescriptorSlotPairs
    (field : Field) (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedFields field
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingPointFields field
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold emittedFields
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end CrossingPointFieldStream
end LeanTrominoes.PeriodicOrthocrossing
