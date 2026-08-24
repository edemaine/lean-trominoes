/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyTemplateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Activity-supported crossing carrier-key word semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Activity-supported recipes emit the physical key of every active padded
crossing carrier-node slot, including translated slots outside the old
neighbor-support window. -/
theorem crossingActiveCarrierKeyGuardedWords_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingActiveCarrierKeyGuardedWords
        (descriptorSlotPairTokens pair) =
      ((paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapActiveValue CarrierNode.carrierKey)).map
          (guardedWord CarrierKeyWords.word) := by
  unfold crossingActiveCarrierKeyGuardedWords
    paddedCrossingCarrierNodeCandidates
  rw [descriptorTokens_descriptorSlotPairTokens]
  rw [words_forceSupportedBlocks_eq_map_guardedWord_candidates]
  rw [map_map_template_crossingCarrierKeyRecipeBlocks]
  rw [← map_carrierKey_crossingCarrierNodeTemplateBlocks]
  simp only [List.map_map, Function.comp_def]
  change
    (candidates
      (crossingActivations (descriptorSlotPairTokens pair))
      ((crossingCarrierNodeTemplateBlocks
        (pair.1.1, pair.2.1)).map fun block =>
          block.map (Template.mapActiveValue CarrierNode.carrierKey))).map
        (guardedWord CarrierKeyWords.word) = _
  rw [← candidates_mapActiveValue]
  simp [List.map_map, Function.comp_def]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
