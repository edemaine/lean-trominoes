/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData

/-! # Padded terminal carrier-node streams -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedLastRepresentativeEqualityRows

/-- Padded terminal-node candidates in descriptor-square order. -/
def paddedTerminalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    List (Candidate CarrierNode) :=
  (descriptors ×ˢ descriptors).flatMap
    paddedTerminalCarrierNodeCandidates

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
