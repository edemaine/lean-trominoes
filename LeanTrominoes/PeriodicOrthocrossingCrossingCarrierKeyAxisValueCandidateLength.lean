/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsLength
import LeanTrominoes.ListForallTwoFlattenLength
import LeanTrominoes.PaddedSupportedCandidateBlockLength
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeAlignmentSemantics

/-! # Crossing carrier-key axis/candidate length alignment -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- There is one crossing axis value for every padded crossing carrier-key
candidate of a tagged descriptor-slot pair. -/
theorem crossingCarrierKeyAxisValues_candidate_length
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (crossingCarrierKeyAxisValues
        (descriptorSlotPairTokens pair)).length =
      (paddedCrossingCarrierKeyCandidates pair).length := by
  unfold crossingCarrierKeyAxisValues
  rw [FixedAxisUnaryFields.values_length_of_length_eq _ _
    (crossingCarrierKeyExpandedActives_axis_length
      (descriptorSlotPairTokens pair))]
  rw [crossingCarrierKeyRecipeAxes_length]
  unfold paddedCrossingCarrierKeyCandidates
  rw [PaddedSupportedCandidateBlocks.candidates_length_of_length_eq]
  · exact List.Forall₂.flatten_length_eq
      (crossingCarrierKeyRecipeBlocks_match pair)
  · simp [crossingActivations, crossingCarrierKeyTemplateBlocks]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
