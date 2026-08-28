/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Compact atom words from guarded carrier-key words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace GuardedCarrierKeyCompactAtomWords

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Replace the support bit of one active guarded carrier-key word by the
two-bit compact terminal constructor. Rejection sentinels and malformed
false-headed words contribute no output. -/
def word : List Bool → List (List Bool)
  | true :: key => [[false, false] ++ key]
  | _ => []

/-- Remove rejection sentinels and retag every active carrier-key word. -/
def words (guarded : List (List Bool)) : List (List Bool) :=
  guarded.flatMap word

/-- Compact output selected by one fixed recipe once its block is active. -/
def recipeWords
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipe : Recipe) : List (List Bool) :=
  if recipe.supported then
    [[false, false] ++ CarrierKeyWords.word (recipe.key tokens)]
  else
    []

/-- Compact outputs selected by one active recipe block. -/
def recipeBlockWords
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipes : List Recipe) : List (List Bool) :=
  recipes.flatMap (recipeWords tokens)

end GuardedCarrierKeyCompactAtomWords
end PeriodicOrthocrossing
end LeanTrominoes
