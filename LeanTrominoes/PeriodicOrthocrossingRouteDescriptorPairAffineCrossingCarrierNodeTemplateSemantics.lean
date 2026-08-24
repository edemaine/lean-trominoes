/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateData

/-! # Values of crossing carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- One retention-shift template carries the four semantic boundary nodes of
its explicitly translated crossing record. -/
theorem occurrencePairCrossingCarrierNodeShiftTemplateBlock_values
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map Template.value =
      crossingRecordCarrierBoundaryNodes
        (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
          (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
            (occurrences.1.evalPair .first pair,
              occurrences.2.evalPair .second pair)) shift) := by
  rfl

/-- Flattening every retention shift for one affine occurrence pair gives
the exact retained crossing-boundary node block. -/
theorem occurrencePairCrossingCarrierNodeTemplateBlock_values
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map Template.value =
      (occurrencePairRetainedCrossingRecordBlockAtPeriod
        pair.1.gridSize
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair)).flatMap
            crossingRecordCarrierBoundaryNodes := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairRetainedCrossingRecordBlockAtPeriod
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact occurrencePairCrossingCarrierNodeShiftTemplateBlock_values
    pair occurrences shift

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
