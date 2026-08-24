/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyGuardedWordData
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairComponentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics

/-! # Paired semantics of crossing source-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

theorem componentWords_crossingCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (paddedCrossingCarrierNodeCandidates pair)) =
      ⟨crossingSourceKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [← crossingSourceKeyRecipePairWords_eq_candidates,
    componentWords_words,
    componentRecipeBlocks_crossingSourceKeyRecipePairBlocks]
  rfl

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
