/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData

/-! # Slot-major affine crossing carrier-key candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Compact carrier-key values selected by one canonical descriptor-slot
pair. -/
def crossingCarrierKeyActiveValues
    (pair : TaggedDescriptor × TaggedDescriptor) :
    List (Nat × Nat × Cell) :=
  activeValues
    (crossingActivations (descriptorSlotPairTokens pair))
    (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1))

/-- Fixed padded carrier-key candidates selected by one canonical
descriptor-slot pair. -/
def paddedCrossingCarrierKeyCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      (Nat × Nat × Cell)) :=
  candidates
    (crossingActivations (descriptorSlotPairTokens pair))
    (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1))

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
