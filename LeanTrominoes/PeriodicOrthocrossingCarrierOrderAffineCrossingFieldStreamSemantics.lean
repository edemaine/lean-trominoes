/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingFieldStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical semantics of crossing order-coordinate field streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingOrderFieldStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem emittedFields_encodeDescriptorSlotPairs
    (keepPositive : Bool)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedFields keepPositive
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields
            keepPositive
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold emittedFields
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [blockFields]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end CrossingOrderFieldStream
end LeanTrominoes.PeriodicOrthocrossing
