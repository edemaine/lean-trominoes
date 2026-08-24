/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateData

/-! # Slot-major affine crossing carrier-node candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Candidate carrier-node templates for a slot and runtime descriptor pair. -/
def Slot.carrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :=
  RouteDescriptorPairAffine.occurrencePairCrossingCarrierNodeTemplateBlock
    pair slot.occurrences

/-- Candidate carrier-node blocks aligned with `crossingSlots`. -/
def crossingCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :=
  crossingSlots.map fun slot => slot.carrierNodeTemplateBlock pair

/-- Fixed padded carrier-node candidates selected by one canonical
descriptor-slot pair. -/
def paddedCrossingCarrierNodeCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      CarrierNode) :=
  candidates
    (crossingActivations (descriptorSlotPairTokens pair))
    (crossingCarrierNodeTemplateBlocks (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
