/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Activity-supported carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Retain a recipe's key data while making every active slot supported. -/
def Recipe.forceSupported (recipe : Recipe) : Recipe :=
  { recipe with supported := true }

/-- Force support throughout a fixed recipe-block family. -/
def forceSupportedBlocks (blocks : List (List Recipe)) :
    List (List Recipe) :=
  blocks.map fun block => block.map Recipe.forceSupported

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
