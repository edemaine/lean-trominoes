/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCrossingCarrierKeyBlockLength
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRecipeWordLength
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueCandidateLength
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyCandidateSemantics

/-! # Crossing order-coordinate candidate lengths -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- One normalized crossing order coordinate is emitted for every padded
crossing carrier-node candidate of a canonical tagged pair. -/
theorem crossingOrderFields_length_candidates
    (keepPositive : Bool)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (crossingOrderFields keepPositive
      (descriptorSlotPairTokens pair)).length =
      (paddedCrossingCarrierNodeCandidates pair).length := by
  calc
    _ = crossingOrderExpressions.length := by
      exact RouteDescriptorPairAffine.normalizedFields_length _ _ _
    _ = crossingCarrierKeyRecipeBlocks.flatten.length :=
      crossingOrderExpressions_length_eq_carrierKeyRecipes
    _ = (crossingCarrierKeyAxisValues
          (descriptorSlotPairTokens pair)).length := by
      unfold crossingCarrierKeyAxisValues
      rw [FixedAxisUnaryFields.values_length_of_length_eq _ _
        (crossingCarrierKeyExpandedActives_axis_length
          (descriptorSlotPairTokens pair))]
      exact crossingCarrierKeyRecipeAxes_length.symm
    _ = (paddedCrossingCarrierKeyCandidates pair).length :=
      crossingCarrierKeyAxisValues_candidate_length pair
    _ = (paddedCrossingCarrierNodeCandidates pair).length := by
      have mapped := congrArg List.length
        (map_carrierKey_paddedCrossingCarrierNodeCandidates pair)
      rw [List.length_map] at mapped
      exact mapped.symm

/-- Concatenating canonical tagged-pair blocks preserves the exact candidate
count alignment. -/
theorem crossingOrderFields_length_candidateBlocks
    (keepPositive : Bool)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    (pairs.flatMap fun pair =>
      crossingOrderFields keepPositive
        (descriptorSlotPairTokens pair)).length =
      (pairs.flatMap paddedCrossingCarrierNodeCandidates).length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [crossingOrderFields_length_candidates, induction]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
