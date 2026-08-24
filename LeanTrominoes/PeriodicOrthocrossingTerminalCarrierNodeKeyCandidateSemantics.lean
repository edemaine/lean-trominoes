/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierNodeKeyTemplateBlockSemantics

/-! # Carrier-key projection of terminal-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem map_carrierKey_paddedTerminalCarrierNodeCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue CarrierNode.carrierKey) =
      paddedTerminalCarrierKeyCandidates pair := by
  unfold paddedTerminalCarrierNodeCandidates
    paddedTerminalCarrierKeyCandidates
  rw [candidates_mapValue]
  rw [map_carrierKey_terminalCarrierNodeTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
