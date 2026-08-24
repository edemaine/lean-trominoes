/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCrossingRecordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateData

/-! # Source keys of reconstructed affine crossing boundaries -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

theorem sourceKeyPair_occurrencePairCrossingBoundary
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence)
    (shift : Cell) (side : CrossingSide) :
    CarrierNodeSourceKeys.pair
        (CarrierNode.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair))
              shift,
            side⟩) =
      (CarrierNodeSourceKeys.taggedKey
          (occurrences.1.carrierKeyAtShift .first pair shift)
          (CarrierNodeSourceKeys.crossingSideTag side),
        occurrences.2.carrierKeyAtShift .second pair shift) := by
  rw [crossingRecordPeriodTranslateAtPeriod_occurrencePairCrossingRecord]
  rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
