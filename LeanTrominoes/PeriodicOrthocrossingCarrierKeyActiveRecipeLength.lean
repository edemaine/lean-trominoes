/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationData

/-! # Length preservation of activity-supported recipe blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem forceSupportedBlocks_flatten_length
    (blocks : List (List Recipe)) :
    (forceSupportedBlocks blocks).flatten.length =
      blocks.flatten.length := by
  simp only [List.length_flatten]
  unfold forceSupportedBlocks
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro block _blockMember
  simp

/-- Forcing support changes no block length, hence preserves the activation
word expanded once per recipe. -/
@[simp] theorem expandedActives_forceSupportedBlocks
    (actives : List Bool) (blocks : List (List Recipe)) :
    expandedActives actives (forceSupportedBlocks blocks) =
      expandedActives actives blocks := by
  induction actives generalizing blocks with
  | nil => cases blocks <;> rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          simp only [forceSupportedBlocks, List.map_cons,
            expandedActives, List.length_map]
          change List.replicate block.length active ++
              expandedActives actives (forceSupportedBlocks blocks) =
            List.replicate block.length active ++
              expandedActives actives blocks
          rw [induction blocks]

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
