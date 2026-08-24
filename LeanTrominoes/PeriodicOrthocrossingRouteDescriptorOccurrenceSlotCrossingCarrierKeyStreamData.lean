/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Slot-major crossing carrier-key streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Compact active carrier-key values in exact
`descriptor₁, slot₁, descriptor₂, slot₂` order. -/
def crossingCarrierKeyActiveValueStream
    (descriptors : List RouteDescriptor) :
    List (Nat × Nat × Cell) :=
  (taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors).flatMap
      crossingCarrierKeyActiveValues

/-- Fixed padded carrier-key candidates in exact
`descriptor₁, slot₁, descriptor₂, slot₂` order. -/
def paddedCrossingCarrierKeyCandidateStream
    (descriptors : List RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      (Nat × Nat × Cell)) :=
  (taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors).flatMap
      paddedCrossingCarrierKeyCandidates

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
