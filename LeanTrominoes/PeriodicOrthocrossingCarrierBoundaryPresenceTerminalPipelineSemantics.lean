/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceSemanticWordSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorStreamSemantics

/-! # Terminal semantics of the carrier boundary-presence pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

theorem terminalFields_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalFields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((CarrierBoundaryPresenceField.terminalKeys descriptors).map
          (GuardedPresenceFieldProjector.value false)) := by
  unfold terminalFields
  rw [CarrierActiveKeyRecipeStream.terminalTokens_descriptorWords,
    TerminalActiveCarrierKeyRecipeStream.guardedWords_eq_presenceSemanticWords]
  exact GuardedPresenceFieldProjector.output_encode_semanticWords
    false (CarrierBoundaryPresenceField.terminalKeys descriptors)

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing

end
