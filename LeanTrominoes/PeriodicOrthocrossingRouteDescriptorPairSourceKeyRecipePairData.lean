/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Explicit pairs of guarded source-key component recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open RouteDescriptorPairCarrierKeyWordRecipes

abbrev RecipePair := Recipe × Recipe

def wordPair (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipes : RecipePair) : List Bool × List Bool :=
  (recipes.1.word tokens active, recipes.2.word tokens active)

def words (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Bool → List (List RecipePair) →
      List (List Bool × List Bool)
  | active :: actives, block :: blocks =>
      block.map (wordPair tokens active) ++ words tokens actives blocks
  | _, _ => []

def componentRecipeBlock (block : List RecipePair) : List Recipe :=
  block.flatMap fun recipes => [recipes.1, recipes.2]

def componentRecipeBlocks (blocks : List (List RecipePair)) :
    List (List Recipe) :=
  blocks.map componentRecipeBlock

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
