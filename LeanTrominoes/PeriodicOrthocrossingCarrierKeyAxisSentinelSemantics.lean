/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisPipelineSemantics

/-! # Physical semantics of the carrier-key axis sentinel -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisPipeline

/-- A single physical delimiter after the compiled axis fields is precisely
the unary encoding of the semantic zero sentinel. -/
theorem fields_appendSentinel_descriptorWords
    (descriptors : List RouteDescriptor) :
    fields (RouteDescriptorBinaryWords.words descriptors) ++
        [UnaryFieldEncoderMachine.Symbol.delimiter] =
      UnaryFieldEncoderMachine.unaryFields
        (CarrierKeyAxisStream.valuesWithSentinel descriptors) := by
  rw [fields_descriptorWords]
  simp [CarrierKeyAxisStream.valuesWithSentinel,
    UnaryFieldEncoderMachine.unaryField]

end CarrierKeyAxisPipeline
end LeanTrominoes.PeriodicOrthocrossing
