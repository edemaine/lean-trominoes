/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingBoundarySourceKeyPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipePairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchData

/-! # Alignment of one crossing source-key recipe pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairSourceKeyRecipePairs

theorem occurrencePairCrossingSourceKeyRecipePair_matchesNode
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence)
    (shift : Cell) (side : CrossingSide) (supported : Bool) :
    MatchesNode (RouteDescriptorPairFieldTags.descriptorPairTokens pair)
      (occurrences.1.taggedSourceKeyRecipeAtShift .first shift side,
        occurrences.2.sourceKeyRecipeAtShift .second shift)
      (⟨CarrierNode.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair))
              shift,
            side⟩,
        supported⟩ : Template CarrierNode) := by
  have boundaryKeys := sourceKeyPair_occurrencePairCrossingBoundary
    pair occurrences shift side
  have firstMatch :=
    (occurrences.1.taggedSourceKeyRecipeAtShift
      .first shift side).matches_template_descriptorPairTokens pair
  have secondMatch :=
    (occurrences.2.sourceKeyRecipeAtShift
      .second shift).matches_template_descriptorPairTokens pair
  unfold MatchesNode
  dsimp only
  rw [boundaryKeys]
  refine ⟨?_, ?_, rfl, rfl⟩
  · simpa [Occurrence.taggedSourceKeyRecipeAtShift, Recipe.template,
      CarrierNodeSourceKeys.taggedKey, Occurrence.carrierKeyAtShift,
      occurrenceCarrierKey, Occurrence.evalPair,
      PeriodicGridDrawing.SegmentOccurrenceKey, descriptorAt]
      using firstMatch.1
  · simpa [Occurrence.sourceKeyRecipeAtShift, Recipe.template,
      Occurrence.carrierKeyAtShift, occurrenceCarrierKey,
      Occurrence.evalPair, PeriodicGridDrawing.SegmentOccurrenceKey,
      descriptorAt]
      using secondMatch.1

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
