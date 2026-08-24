/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeSemantics

/-! # Guarded-word semantics of activity-supported carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open PaddedSupportedCandidateBlocks
open PaddedSupportedCandidateWords
open RouteDescriptorPairFieldTags

/-- Every forced-support recipe matches its own interpreted template on a
canonical descriptor pair. -/
theorem forceSupportedBlocks_match
    (pair : RouteDescriptor × RouteDescriptor)
    (blocks : List (List Recipe)) :
    List.Forall₂
      (List.Forall₂ (Recipe.Matches (descriptorPairTokens pair)))
      (forceSupportedBlocks blocks)
      ((forceSupportedBlocks blocks).map fun block =>
        block.map (Recipe.template pair)) := by
  induction blocks with
  | nil => exact List.Forall₂.nil
  | cons block blocks induction =>
      apply List.Forall₂.cons
      · induction block with
        | nil => exact List.Forall₂.nil
        | cons recipe recipes inductionRecipes =>
            exact List.Forall₂.cons
              (recipe.forceSupported.matches_template_descriptorPairTokens
                pair)
              inductionRecipes
      · exact induction

/-- Forced-support recipe words are exactly the guarded words of the
activity-supported value projection of their original interpreted blocks. -/
theorem words_forceSupportedBlocks_eq_map_guardedWord_candidates
    (pair : RouteDescriptor × RouteDescriptor) (actives : List Bool)
    (blocks : List (List Recipe)) :
    words (descriptorPairTokens pair) actives
        (forceSupportedBlocks blocks) =
      (candidates actives
        ((blocks.map fun block =>
          block.map (Recipe.template pair)).map fun block =>
            block.map (Template.mapActiveValue id))).map
        (guardedWord CarrierKeyWords.word) := by
  rw [← forceSupportedBlocks_map_template]
  exact words_eq_map_guardedWord_candidates
    (descriptorPairTokens pair) actives
    (forceSupportedBlocks blocks)
    ((forceSupportedBlocks blocks).map fun block =>
      block.map (Recipe.template pair))
    (forceSupportedBlocks_match pair blocks)

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
