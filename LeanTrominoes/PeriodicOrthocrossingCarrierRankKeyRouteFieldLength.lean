/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldData

/-! # Alignment length of the carrier-key route field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

/-- The route field has one value for every compact source-key candidate,
plus the rejection sentinel used by representative lookup. -/
theorem alignedValuesWithSentinel_length_sourceKeyCandidates
    (descriptors : List RouteDescriptor) :
    (alignedValuesWithSentinel descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  simp [alignedValuesWithSentinel,
    CarrierActiveKeyRecipeStream.semanticKeys,
    PaddedSupportedLastRepresentativeEqualityRows.values,
    paddedCarrierSourceKeyCandidateStream]

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
