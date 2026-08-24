/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipePairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchData

/-! # Alignment of one terminal source-key recipe pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairSourceKeyRecipePairs

theorem terminalSourceKeyRecipePair_matchesNode
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment)
    (translate : Cell) (endpoint : SegmentEnd) :
    MatchesNode (RouteDescriptorPairFieldTags.descriptorPairTokens pair)
      (terminalSourceKeyRecipePair segmentIndex translate endpoint)
      (⟨CarrierNode.terminal
          ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
            translate, endpoint⟩,
        true⟩ : Template CarrierNode) := by
  have keyMatch :=
    (terminalSourceKeyRecipe segmentIndex translate endpoint).matches_template_descriptorPairTokens
      pair
  unfold MatchesNode terminalSourceKeyRecipePair
  dsimp only
  refine ⟨?_, ?_, rfl, rfl⟩
  · simpa [terminalSourceKeyRecipe, Recipe.template,
      CarrierNodeSourceKeys.pair, CarrierNodeSourceKeys.taggedKey,
      CarrierNode.carrierKey, SegmentTerminal.carrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey] using keyMatch.1
  · simpa [terminalSourceKeyRecipe, Recipe.template,
      CarrierNodeSourceKeys.pair, CarrierNodeSourceKeys.taggedKey,
      CarrierNode.carrierKey, SegmentTerminal.carrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey] using keyMatch.1

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
