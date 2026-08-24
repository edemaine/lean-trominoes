/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData

/-! # Fixed terminal carrier-node slots for route-descriptor pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairFieldTags

/-- Padded terminal carrier-node slots of one descriptor pair. -/
def paddedTerminalCarrierNodeCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      CarrierNode) :=
  candidates
    (terminalCarrierKeyActivations (descriptorPairTokens pair))
    (terminalCarrierNodeTemplateBlocks pair)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
