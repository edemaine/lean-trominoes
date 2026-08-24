/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Flattened activation words for carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Repeat each block activation once for every recipe in that block,
stopping at the shorter list on malformed unequal-length inputs. -/
def expandedActives : List Bool → List (List Recipe) → List Bool
  | active :: actives, block :: blocks =>
      List.replicate block.length active ++ expandedActives actives blocks
  | _, _ => []

/-- The flattened recipe interpretation expected by the batched emitter. -/
def flattenedWords
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe)) :
    List (List Bool) :=
  List.zipWith (fun active recipe => recipe.word tokens active)
    (expandedActives actives blocks) blocks.flatten

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
