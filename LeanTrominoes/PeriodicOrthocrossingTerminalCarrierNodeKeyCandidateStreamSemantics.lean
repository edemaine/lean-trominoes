/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierNodeKeyCandidateSemantics

/-! # Carrier-key projection of terminal-node candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem map_carrierKey_paddedTerminalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue CarrierNode.carrierKey) =
      paddedTerminalCarrierKeyCandidateStream descriptors := by
  unfold paddedTerminalCarrierNodeCandidateStream
    paddedTerminalCarrierKeyCandidateStream
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_carrierKey_paddedTerminalCarrierNodeCandidates pair

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
