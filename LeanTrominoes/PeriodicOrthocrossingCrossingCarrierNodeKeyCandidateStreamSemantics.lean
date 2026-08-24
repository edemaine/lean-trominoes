/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData

/-! # Carrier-key projection of padded crossing-node streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem map_carrierKey_paddedCrossingCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedCrossingCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue CarrierNode.carrierKey) =
      paddedCrossingCarrierKeyCandidateStream descriptors := by
  unfold paddedCrossingCarrierNodeCandidateStream
    paddedCrossingCarrierKeyCandidateStream
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_carrierKey_paddedCrossingCarrierNodeCandidates pair

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
