/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingPipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingTagSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisStreamSemantics

/-! # Exact crossing carrier-key axis pipeline semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisCrossingPipeline

@[simp] theorem fields_descriptorWords
    (descriptors : List RouteDescriptor) :
    fields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (CarrierKeyAxisStream.crossingValues descriptors) := by
  unfold fields CarrierKeyAxisStream.crossingValues
  rw [CarrierKeyAxisCrossingTags.tags_descriptorWords,
    CrossingCarrierKeyAxisStream.emittedFields_encodeDescriptorSlotPairs]

end CarrierKeyAxisCrossingPipeline
end LeanTrominoes.PeriodicOrthocrossing
