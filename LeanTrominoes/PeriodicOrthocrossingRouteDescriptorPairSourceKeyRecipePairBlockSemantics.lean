/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairData

/-! # Component semantics of one source-key recipe-pair block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open RouteDescriptorPairCarrierKeyWordRecipes

theorem flatMap_wordPair_eq_map_componentRecipeBlock
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (block : List RecipePair) :
    (block.map (wordPair tokens active)).flatMap
        (fun pair => [pair.1, pair.2]) =
      (componentRecipeBlock block).map (Recipe.word tokens active) := by
  induction block with
  | nil => rfl
  | cons recipes block induction =>
      simp [wordPair, componentRecipeBlock, induction]

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
