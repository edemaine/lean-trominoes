/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceCrossingPipelineSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalPipelineSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Complete semantics of the carrier boundary-presence pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

theorem fields_descriptorWords (descriptors : List RouteDescriptor) :
    fields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (CarrierBoundaryPresenceField.alignedValuesWithSentinel
          descriptors) := by
  unfold fields CarrierBoundaryPresenceField.alignedValuesWithSentinel
  rw [terminalFields_descriptorWords, crossingFields_descriptorWords]
  simp [UnaryFieldEncoderMachine.unaryField, List.append_assoc]

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing

end
