/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCrossingCandidateLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentPairLength
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyCandidateStreamPairSemantics

/-! # Crossing source-key stream lengths for carrier order coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Crossing source-component and order-value streams remain aligned after
concatenating the full tagged descriptor-slot pair product. -/
theorem guardedWords_length_twice_orderFields
    (keepPositive : Bool) (descriptors : List RouteDescriptor) :
    (guardedWords
      (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors)).length =
      2 * ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields
            keepPositive
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)).length := by
  have componentEq := congrArg
    (fun input : DelimitedBinaryWords.Input => input.words.length)
    (RouteDescriptorOccurrenceSlotCrossing.componentWords_paddedCrossingCarrierNodeCandidateStream
      descriptors)
  rw [sourceKeyComponentWords_length] at componentEq
  have candidateEq :=
    RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields_length_candidateBlocks
      keepPositive
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)
  unfold RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
    at componentEq
  calc
    _ = 2 * ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap
          RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates).length :=
      componentEq.symm
    _ = _ := congrArg (fun count => 2 * count) candidateEq.symm

end CrossingSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
