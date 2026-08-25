/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeySemanticWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorStreamSemantics

/-! # Route-field projection of the active carrier-key stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Route projection emits one route index per padded carrier-node slot,
followed by the unary-zero representative-lookup sentinel. -/
theorem CarrierActiveKeyRecipeStream.routeFieldOutput_descriptorWords
    (descriptors : List RouteDescriptor) :
    CarrierKeyRouteFieldProjector.output
        (CarrierActiveKeyRecipeStream.emittedTokens
          (RouteDescriptorBinaryWords.words descriptors)) =
      UnaryFieldEncoderMachine.unaryFields
        ((CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
          CarrierKeyRouteFieldProjector.value ++ [0]) := by
  rw [CarrierActiveKeyRecipeStream.emittedTokens_descriptorWords,
    CarrierActiveKeyRecipeStream.guardedWords_eq_semanticWords]
  exact CarrierKeyRouteFieldProjector.output_encode_semanticWords
    (CarrierActiveKeyRecipeStream.semanticKeys descriptors)

end LeanTrominoes.PeriodicOrthocrossing

end
