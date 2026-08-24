/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData

/-! # Activity semantics of crossing carrier-node candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Filtering inactive slots from the padded slot-major stream gives its
exact compact crossing-node active-value stream. -/
theorem filterMap_paddedCrossingCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedCrossingCarrierNodeCandidateStream descriptors).filterMap
        Candidate.value =
      (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          activeValues
            (crossingActivations (descriptorSlotPairTokens pair))
            (crossingCarrierNodeTemplateBlocks
              (pair.1.1, pair.2.1)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
    paddedCrossingCarrierNodeCandidates
  exact filterMap_value_flatMap_candidates
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)
    (fun pair => crossingActivations (descriptorSlotPairTokens pair))
    (fun pair =>
      crossingCarrierNodeTemplateBlocks (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
