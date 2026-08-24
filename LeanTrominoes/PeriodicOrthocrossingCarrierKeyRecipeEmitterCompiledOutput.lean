/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTokenSemantics

/-! # Semantic output underlying compiled carrier-key recipe tokens -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

def compiledOutput (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    DelimitedBinaryWords.Input :=
  ⟨List.zipWith (CarrierKeyRecipeEmitter.preparedWord input)
    (scanState (initialState recipes.length) input).actives.toList recipes⟩

/-- Every physical compiled block is a canonical delimiter encoding. -/
@[simp] theorem compiledTokens_eq_encode_compiledOutput
    (recipes : List Recipe) (input : List CarrierKeyRecipeEmitter.Token) :
    compiledTokens recipes input =
      DelimitedBinaryWords.encode (compiledOutput recipes input) := by
  unfold compiledTokens allRecipeTokens recipeBlocks compiledOutput
    DelimitedBinaryWords.encode
  generalize activeEq :
    (scanState (initialState recipes.length) input).actives.toList = actives
  clear activeEq
  induction actives generalizing recipes with
  | nil => rfl
  | cons active actives induction =>
      cases recipes with
      | nil => rfl
      | cons recipe recipes =>
          simp only [List.zipWith_cons_cons, List.flatten_cons,
            List.flatMap_cons]
          rw [tokenBlock_eq_wordTokens, induction recipes]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
