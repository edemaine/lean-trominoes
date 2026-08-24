/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyGuardedWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData

/-! # Paired source-key words of the padded crossing-node stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords

theorem componentWords_paddedCrossingCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (paddedCrossingCarrierNodeCandidateStream descriptors)) =
      ⟨CrossingSourceKeyRecipeStream.guardedWords
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
    paddedCrossingCarrierNodeCandidateStream
    CrossingSourceKeyRecipeStream.guardedWords
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair _pairMember
  have pairEq := congrArg DelimitedBinaryWords.Input.words
    (componentWords_crossingCandidates pair)
  simpa [DelimitedBinaryWordGuardedPairMerge.componentWords,
    CarrierNodeSourceKeyCandidateWords.componentPairs] using pairEq

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
