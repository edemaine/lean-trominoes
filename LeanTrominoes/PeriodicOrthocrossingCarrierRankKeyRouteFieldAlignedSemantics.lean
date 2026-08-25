/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRouteFieldProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldData

/-! # Aligned route-field semantics of the active carrier-key pipeline -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

/-- The active carrier-key emitter followed by route projection produces
one aligned route-index field per padded carrier node and one sentinel. -/
theorem output_emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    CarrierKeyRouteFieldProjector.output
        (CarrierActiveKeyRecipeStream.emittedTokens
          (RouteDescriptorBinaryWords.words descriptors)) =
      UnaryFieldEncoderMachine.unaryFields
        (alignedValuesWithSentinel descriptors) := by
  simpa only [alignedValuesWithSentinel] using
    CarrierActiveKeyRecipeStream.routeFieldOutput_descriptorWords descriptors

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
