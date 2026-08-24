/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisActiveBlocksSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Key-derived crossing axes of one tagged descriptor-slot pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- For one matched tagged descriptor-slot pair, every padded crossing-axis
value is the descriptor-level datum of its carrier-key candidate. -/
theorem crossingCarrierKeyAxisValues_eq_map_candidates_of_matches
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteDescriptorPairAffine.RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1)
    (firstDescriptorMember : pair.1.1 ∈ descriptors)
    (secondDescriptorMember : pair.2.1 ∈ descriptors) :
    crossingCarrierKeyAxisValues (descriptorSlotPairTokens pair) =
      (paddedCrossingCarrierKeyCandidates pair).map
        (RouteDescriptorCarrierKeyAxisDatum.value descriptors ∘
          Candidate.value) := by
  unfold crossingCarrierKeyAxisValues crossingCarrierKeyRecipeAxes
    paddedCrossingCarrierKeyCandidates
  rw [crossingCarrierKeyExpandedActives_eq_axisBlockActives]
  exact FixedAxisUnaryFields.values_blockActives_eq_map_candidates_of_active
    (RouteDescriptorCarrierKeyAxisDatum.value descriptors)
    (crossingActivations (descriptorSlotPairTokens pair))
    crossingCarrierKeyRecipeAxisBlocks
    (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1))
    (crossingCarrierKeyActiveDatumBlocks_of_matches
      descriptors selfIndexed firstShape secondShape pair
      firstMatches secondMatches firstDescriptorMember
      secondDescriptorMember)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
