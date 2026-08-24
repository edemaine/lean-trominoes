/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisCrossingPipelineSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisPipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisTerminalPipelineSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Exact complete padded carrier-key axis semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisPipeline

@[simp] theorem fields_descriptorWords
    (descriptors : List RouteDescriptor) :
    fields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (CarrierKeyAxisStream.values descriptors) := by
  unfold fields CarrierKeyAxisStream.values
  rw [CarrierKeyAxisTerminalPipeline.fields_descriptorWords,
    CarrierKeyAxisCrossingPipeline.fields_descriptorWords,
    UnaryFieldEncoderMachine.unaryFields_append]

end CarrierKeyAxisPipeline
end LeanTrominoes.PeriodicOrthocrossing
