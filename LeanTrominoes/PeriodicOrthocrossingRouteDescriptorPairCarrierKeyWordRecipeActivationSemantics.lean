/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationData

/-! # Semantics of flattened carrier-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Zipping a repeated head activation across one complete block separates
from the aligned tail zip. -/
theorem zipWith_replicate_length_append
    (function : Bool → Recipe → List Bool)
    (active : Bool) (block : List Recipe)
    (tailActives : List Bool) (tailRecipes : List Recipe) :
    List.zipWith function
        (List.replicate block.length active ++ tailActives)
        (block ++ tailRecipes) =
      block.map (function active) ++
        List.zipWith function tailActives tailRecipes := by
  induction block with
  | nil => rfl
  | cons recipe block induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, List.zipWith_cons_cons, List.map_cons]
      rw [induction]

/-- Flattening activation bits across recipe blocks preserves the exact
left-to-right guarded-word stream. -/
theorem words_eq_flattenedWords
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe)) :
    words tokens actives blocks =
      flattenedWords tokens actives blocks := by
  induction actives generalizing blocks with
  | nil =>
      simp [words, flattenedWords, expandedActives]
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          rw [words]
          unfold flattenedWords
          rw [expandedActives, List.flatten_cons,
            zipWith_replicate_length_append]
          change block.map (Recipe.word tokens active) ++
              words tokens actives blocks =
            block.map (Recipe.word tokens active) ++
              flattenedWords tokens actives blocks
          rw [induction blocks]

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
