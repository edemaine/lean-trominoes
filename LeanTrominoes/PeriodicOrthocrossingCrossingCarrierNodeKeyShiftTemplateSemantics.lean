/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateData

/-! # Carrier-key projection of one crossing-node shift block -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem map_carrierKey_occurrencePairCrossingCarrierNodeShiftTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map
        (Template.mapValue CarrierNode.carrierKey) =
      occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift := by
  simp [occurrencePairCrossingCarrierNodeShiftTemplateBlock,
    occurrencePairCrossingCarrierKeyShiftTemplateBlock,
    Template.mapValue, CarrierNode.carrierKey,
    CrossingBoundary.carrierKey,
    crossingRecordPeriodTranslateAtPeriod,
    occurrencePairCrossingRecordAtPeriod,
    Occurrence.carrierKeyAtShift, occurrenceCarrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    Occurrence.evalPair]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
