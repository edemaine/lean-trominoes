/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairBlockSemantics

/-! # Component semantics of source-key recipe-pair streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open RouteDescriptorPairCarrierKeyWordRecipes

theorem componentWords_words
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List RecipePair)) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (words tokens actives blocks) =
      ⟨RouteDescriptorPairCarrierKeyWordRecipes.words tokens actives
        (componentRecipeBlocks blocks)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  induction actives generalizing blocks with
  | nil => rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          unfold words RouteDescriptorPairCarrierKeyWordRecipes.words
            componentRecipeBlocks
          simp only [List.map_cons, List.flatMap_append]
          rw [flatMap_wordPair_eq_map_componentRecipeBlock,
            induction blocks]
          rfl

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
