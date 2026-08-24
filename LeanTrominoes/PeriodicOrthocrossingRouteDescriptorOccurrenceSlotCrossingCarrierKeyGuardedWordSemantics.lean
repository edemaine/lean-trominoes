/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyData

/-! # Guarded words of padded crossing carrier-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateWords
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Batched crossing recipes emit exactly the guarded words of the existing
padded crossing candidate block. -/
theorem crossingCarrierKeyGuardedWords_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingCarrierKeyGuardedWords (descriptorSlotPairTokens pair) =
      (paddedCrossingCarrierKeyCandidates pair).map
        (guardedWord CarrierKeyWords.word) := by
  unfold crossingCarrierKeyGuardedWords
    paddedCrossingCarrierKeyCandidates
  exact words_eq_map_guardedWord_candidates
    (descriptorTokens (descriptorSlotPairTokens pair))
    (crossingActivations (descriptorSlotPairTokens pair))
    crossingCarrierKeyRecipeBlocks
    (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1))
    (crossingCarrierKeyRecipeBlocks_match pair)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
