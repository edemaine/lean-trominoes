/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData

/-! # Alignment lengths of all carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- Every key column has one value per compact source-key candidate plus
the representative-lookup rejection sentinel. -/
theorem alignedValuesWithSentinel_length_sourceKeyCandidates
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (alignedValuesWithSentinel field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  simp [alignedValuesWithSentinel,
    CarrierActiveKeyRecipeStream.semanticKeys,
    PaddedSupportedLastRepresentativeEqualityRows.values,
    paddedCarrierSourceKeyCandidateStream]

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
