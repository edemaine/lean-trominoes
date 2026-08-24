/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPairOccurrenceSemantics

/-! # Carrier nodes selected by one descriptor-slot pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- For locally selected descriptors, one slot-pair block emits exactly the
retained boundary nodes of its optional canonical semantic crossing. -/
theorem crossingCarrierNodeActiveValues_eq_optionalFilteredPair_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    activeValues
        (crossingActivations (descriptorSlotPairTokens pair))
        (crossingCarrierNodeTemplateBlocks (pair.1.1, pair.2.1)) =
      (List.optionalFilteredPair
        (canonicalOrientedOccurrencePairAtPeriod pair.1.1.gridSize)
        (occurrenceAtSlot pair.1)
        (occurrenceAtSlot pair.2)).toList.flatMap fun occurrencePair =>
          (occurrencePairRetainedCrossingRecordBlockAtPeriod
            pair.1.1.gridSize occurrencePair).flatMap
              crossingRecordCarrierBoundaryNodes := by
  rw [crossingCarrierNodeActiveValues_eq_occurrenceScan]
  calc
    (crossingSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).flatMap
          (fun slot =>
            (occurrencePairRetainedCrossingRecordBlockAtPeriod
              pair.1.1.gridSize
              (slot.occurrences.1.evalPair .first
                  (pair.1.1, pair.2.1),
                slot.occurrences.2.evalPair .second
                  (pair.1.1, pair.2.1))).flatMap
                    crossingRecordCarrierBoundaryNodes) =
      ((crossingSlots.filter fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair)).map
            (fun slot =>
              (slot.occurrences.1.evalPair .first
                  (pair.1.1, pair.2.1),
                slot.occurrences.2.evalPair .second
                  (pair.1.1, pair.2.1)))).flatMap
            (fun occurrencePair =>
              (occurrencePairRetainedCrossingRecordBlockAtPeriod
                pair.1.1.gridSize occurrencePair).flatMap
                  crossingRecordCarrierBoundaryNodes) := by
        rw [List.flatMap_map]
    _ = _ := by
      rw [map_filter_crossingSlots_eq_optionalFilteredPair_of_matches
        firstShape secondShape pair firstMatches secondMatches]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
