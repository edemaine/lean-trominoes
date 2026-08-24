/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData

/-! # Padded terminal carrier-key candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedLastRepresentativeEqualityRows

/-- Padded terminal-key candidates in descriptor-square order. -/
def paddedTerminalCarrierKeyCandidateStream
    (descriptors : List RouteDescriptor) :
    List (Candidate CarrierKey) :=
  (descriptors ×ˢ descriptors).flatMap
    paddedTerminalCarrierKeyCandidates

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
