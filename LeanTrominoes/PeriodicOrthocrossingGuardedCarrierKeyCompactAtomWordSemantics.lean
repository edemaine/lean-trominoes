/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierKeyCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockData

/-! # Semantics of compacting guarded carrier-key words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace GuardedCarrierKeyCompactAtomWords

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairAffine

/-- Compacting one guarded recipe word keeps exactly an active supported
recipe and removes every rejection sentinel. -/
theorem word_recipe_word
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipe : Recipe) :
    word (Recipe.word tokens active recipe) =
      if active then recipeWords tokens recipe else [] := by
  cases active <;> cases supported : recipe.supported <;>
    simp [word, Recipe.word, recipeWords,
      PaddedSupportedCandidateWords.sentinelWord, supported]

@[simp] theorem words_append
    (first second : List (List Bool)) :
    words (first ++ second) = words first ++ words second := by
  simp [words]

/-- Compacting one aligned guarded recipe block is its compact selected block
when active and is empty otherwise. -/
theorem words_map_recipe_word
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipes : List Recipe) :
    words (recipes.map (Recipe.word tokens active)) =
      if active then recipeBlockWords tokens recipes else [] := by
  induction recipes with
  | nil => simp [words, recipeBlockWords]
  | cons recipe recipes induction =>
      simp only [List.map_cons]
      change word (Recipe.word tokens active recipe) ++
          words (recipes.map (Recipe.word tokens active)) = _
      rw [word_recipe_word, induction]
      cases active <;> simp [recipeBlockWords]

/-- After sentinel removal, guarded recipe emission is exactly ordinary
truth-selected compact block concatenation. -/
theorem words_recipe_words
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe)) :
    words (RouteDescriptorPairCarrierKeyWordRecipes.words
      tokens actives blocks) =
      selectTruthBlocks
        (blocks.map (recipeBlockWords tokens)) actives := by
  induction actives generalizing blocks with
  | nil => simp [RouteDescriptorPairCarrierKeyWordRecipes.words,
      words, selectTruthBlocks]
  | cons active actives induction =>
      cases blocks with
      | nil => simp [RouteDescriptorPairCarrierKeyWordRecipes.words,
          words, selectTruthBlocks]
      | cons block blocks =>
          rw [RouteDescriptorPairCarrierKeyWordRecipes.words,
            words_append,
            words_map_recipe_word, induction]
          cases active <;> simp [selectTruthBlocks]

end GuardedCarrierKeyCompactAtomWords
end PeriodicOrthocrossing
end LeanTrominoes
