/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyTemplateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Carrier-key projection of padded crossing-node candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem map_carrierKey_paddedCrossingCarrierNodeCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapValue CarrierNode.carrierKey) =
      paddedCrossingCarrierKeyCandidates pair := by
  unfold paddedCrossingCarrierNodeCandidates
    paddedCrossingCarrierKeyCandidates
  rw [candidates_mapValue]
  rw [map_carrierKey_crossingCarrierNodeTemplateBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
