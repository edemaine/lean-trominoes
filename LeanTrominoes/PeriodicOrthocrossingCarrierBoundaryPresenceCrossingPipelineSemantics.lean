/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceSemanticWordSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorStreamSemantics

/-! # Crossing semantics of the carrier boundary-presence pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

theorem crossingFields_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingFields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((CarrierBoundaryPresenceField.crossingKeys descriptors).map
          (GuardedPresenceFieldProjector.value true)) := by
  unfold crossingFields
  rw [CarrierActiveKeyRecipeStream.crossingTokens_descriptorWords,
    CrossingActiveCarrierKeyRecipeStream.guardedWords_eq_presenceSemanticWords]
  exact GuardedPresenceFieldProjector.output_encode_semanticWords
    true (CarrierBoundaryPresenceField.crossingKeys descriptors)

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing

end
