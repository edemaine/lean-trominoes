/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueCompilerSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Canonical semantics of crossing carrier-key axis streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingCarrierKeyAxisStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem emittedFields_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedFields
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      UnaryFieldEncoderMachine.unaryFields
        (pairs.flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisValues
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold emittedFields
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisCompiledFields_eq]
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

end CrossingCarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing
