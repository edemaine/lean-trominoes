/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData

/-! # Slot-major crossing carrier-node streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Fixed padded carrier-node candidates in exact
`descriptor₁, slot₁, descriptor₂, slot₂` order. -/
def paddedCrossingCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      CarrierNode) :=
  (taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors).flatMap
      paddedCrossingCarrierNodeCandidates

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
