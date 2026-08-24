/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierNodeKeyCandidateStreamSemantics

/-! # Carrier-key projection of the complete padded carrier-node stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem map_carrierKey_paddedCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue CarrierNode.carrierKey) =
      paddedCarrierKeyCandidateStream descriptors := by
  simp [paddedCarrierNodeCandidateStream,
    paddedCarrierKeyCandidateStream]

end LeanTrominoes.PeriodicOrthocrossing

end
