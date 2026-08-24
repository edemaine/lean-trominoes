/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActiveMap
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeTemplateSemantics

/-! # Semantics of activity-supported carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open PaddedSupportedCandidateBlocks

@[simp] theorem Recipe.forceSupported_key
    (tokens : List RouteDescriptorPairFieldTags.Token) (recipe : Recipe) :
    recipe.forceSupported.key tokens = recipe.key tokens := by
  rfl

@[simp] theorem Recipe.forceSupported_template
    (pair : RouteDescriptor × RouteDescriptor) (recipe : Recipe) :
    recipe.forceSupported.template pair =
      (recipe.template pair).mapActiveValue id := by
  cases recipe
  rfl

@[simp] theorem forceSupportedBlocks_map_template
    (pair : RouteDescriptor × RouteDescriptor)
    (blocks : List (List Recipe)) :
    (forceSupportedBlocks blocks).map
        (fun block => block.map (Recipe.template pair)) =
      (blocks.map fun block => block.map (Recipe.template pair)).map
        fun block => block.map (Template.mapActiveValue id) := by
  simp [forceSupportedBlocks, List.map_map, Function.comp_def]

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
