/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterWordSemantics

/-! # Semantics of compact carrier-key recipe emitter inputs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Compact preparation preserves the exact flat guarded-word stream. -/
@[simp] theorem words_prepared
    (recipes : List Recipe)
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) :
    words recipes (prepared tokens actives) =
      List.zipWith (fun active recipe => recipe.word tokens active)
        actives recipes := by
  unfold words
  rw [activationBits_prepared]
  have build : ∀ (left : List Bool) (right : List Recipe),
      List.zipWith (preparedWord (prepared tokens actives)) left right =
        List.zipWith (fun active recipe => recipe.word tokens active)
          left right := by
    intro left
    induction left with
    | nil => intro _; rfl
    | cons active left induction =>
        intro right
        cases right with
        | nil => rfl
        | cons recipe right =>
            simp only [List.zipWith_cons_cons]
            rw [preparedWord_prepared, induction]
  exact build actives recipes

/-- Compact preparation preserves the semantic delimited-word output. -/
@[simp] theorem output_prepared
    (recipes : List Recipe)
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) :
    output recipes (prepared tokens actives) =
      ⟨List.zipWith (fun active recipe => recipe.word tokens active)
        actives recipes⟩ := by
  unfold output
  rw [words_prepared]

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
