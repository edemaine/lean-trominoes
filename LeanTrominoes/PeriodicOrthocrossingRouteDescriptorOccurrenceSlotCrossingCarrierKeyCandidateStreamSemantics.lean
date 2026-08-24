/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData

/-! # Activity semantics of slot-major crossing carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Filtering inactive option slots from the fixed padded slot-major stream
recovers its exact compact active carrier-key stream. -/
theorem filterMap_paddedCrossingCarrierKeyCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedCrossingCarrierKeyCandidateStream descriptors).filterMap
        Candidate.value =
      crossingCarrierKeyActiveValueStream descriptors := by
  unfold paddedCrossingCarrierKeyCandidateStream
    crossingCarrierKeyActiveValueStream
    paddedCrossingCarrierKeyCandidates
    crossingCarrierKeyActiveValues
  exact filterMap_value_flatMap_candidates
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)
    (fun pair =>
      crossingActivations (descriptorSlotPairTokens pair))
    (fun pair =>
      crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
