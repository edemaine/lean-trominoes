/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyActivationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyTemplateData

/-! # Fixed terminal carrier-key slots for route-descriptor pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Padded terminal carrier-key slots of one descriptor pair. -/
def paddedTerminalCarrierKeyCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate CarrierKey) :=
  candidates
    (terminalCarrierKeyActivations (descriptorPairTokens pair))
    (terminalCarrierKeyTemplateBlocks pair)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
