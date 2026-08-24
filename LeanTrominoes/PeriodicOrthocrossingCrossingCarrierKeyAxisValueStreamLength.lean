/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueCandidateLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamData

/-! # Crossing carrier-key axis-stream length -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- Pairwise crossing axis/candidate alignment extends to the complete
tagged-descriptor-square stream. -/
theorem crossingCarrierKeyAxisValueStream_length
    (descriptors : List RouteDescriptor) :
    ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          crossingCarrierKeyAxisValues
            (descriptorSlotPairTokens pair)).length =
      (paddedCrossingCarrierKeyCandidateStream descriptors).length := by
  unfold paddedCrossingCarrierKeyCandidateStream
  generalize taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors = pairs
  induction pairs with
  | nil => simp only [List.flatMap_nil, List.length_nil]
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [crossingCarrierKeyAxisValues_candidate_length, induction]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
