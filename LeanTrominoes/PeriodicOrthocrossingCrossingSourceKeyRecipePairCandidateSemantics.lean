/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchStreamSemantics

/-! # Crossing source-key recipe pairs as padded node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

theorem crossingSourceKeyRecipePairWords_eq_candidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorTokens (descriptorSlotPairTokens pair))
        (crossingActivations (descriptorSlotPairTokens pair))
        crossingSourceKeyRecipePairBlocks =
      (paddedCrossingCarrierNodeCandidates pair).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  unfold paddedCrossingCarrierNodeCandidates
  apply words_eq_map_componentPair_candidates
  simpa using crossingSourceKeyRecipePairBlocks_matchNode
    (pair.1.1, pair.2.1)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
