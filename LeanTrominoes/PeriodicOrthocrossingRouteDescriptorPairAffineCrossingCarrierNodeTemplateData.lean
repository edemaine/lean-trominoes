/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateData

/-! # Fixed crossing carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- Four boundary-node templates for one retained crossing shift.  The two
horizontal boundaries use first-occurrence support, and the two vertical
boundaries use second-occurrence support. -/
def occurrencePairCrossingCarrierNodeShiftTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    List (Template CarrierNode) :=
  let period := pair.1.gridSize
  let record := crossingRecordPeriodTranslateAtPeriod period
    (occurrencePairCrossingRecordAtPeriod period
      (occurrences.1.evalPair .first pair,
        occurrences.2.evalPair .second pair)) shift
  let firstSupported :=
    occurrences.1.carrierKeyAtShiftSupported shift
  let secondSupported :=
    occurrences.2.carrierKeyAtShiftSupported shift
  [⟨CarrierNode.boundary ⟨record, .left⟩, firstSupported⟩,
    ⟨CarrierNode.boundary ⟨record, .right⟩, firstSupported⟩,
    ⟨CarrierNode.boundary ⟨record, .top⟩, secondSupported⟩,
    ⟨CarrierNode.boundary ⟨record, .bottom⟩, secondSupported⟩]

/-- Complete retained-orbit node template block for one fixed affine
occurrence-pair crossing predicate. -/
def occurrencePairCrossingCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    List (Template CarrierNode) :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingCarrierNodeShiftTemplateBlock pair occurrences)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
