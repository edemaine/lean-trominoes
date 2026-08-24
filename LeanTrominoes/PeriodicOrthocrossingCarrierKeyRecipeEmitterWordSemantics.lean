/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedSemantics

/-! # Word semantics of compact carrier-key recipe preparation -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem preparedKey_prepared
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (recipe : Recipe) :
    preparedKey (prepared tokens actives) recipe = recipe.key tokens := by
  unfold preparedKey Recipe.key
  rw [routeCount_prepared]

@[simp] theorem preparedWord_prepared
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (active : Bool) (recipe : Recipe) :
    preparedWord (prepared tokens actives) active recipe =
      recipe.word tokens active := by
  unfold preparedWord Recipe.word
  rw [preparedKey_prepared]

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
