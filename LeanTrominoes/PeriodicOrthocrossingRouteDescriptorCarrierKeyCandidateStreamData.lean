/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData

/-! # Complete padded carrier-key candidate streams -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

abbrev CarrierKey := Nat × Nat × Cell

/-- Padded terminal-key candidates in descriptor-square order. -/
def paddedTerminalCarrierKeyCandidateStream
    (descriptors : List RouteDescriptor) : List (Candidate CarrierKey) :=
  (descriptors ×ˢ descriptors).flatMap
    RouteDescriptorPairAffine.paddedTerminalCarrierKeyCandidates

/-- Complete padded candidate stream: terminal prefix followed by the exact
`descriptor₁, slot₁, descriptor₂, slot₂` crossing stream. -/
def paddedCarrierKeyCandidateStream
    (descriptors : List RouteDescriptor) : List (Candidate CarrierKey) :=
  paddedTerminalCarrierKeyCandidateStream descriptors ++
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierKeyCandidateStream
      descriptors

end LeanTrominoes.PeriodicOrthocrossing
