/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRecipeSuffixData

/-! # Decomposition of remaining carrier-key recipe blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem recipeBlocks_length (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) :
    (recipeBlocks recipes input state).length = recipes.length := by
  simp [recipeBlocks]

@[simp] theorem recipeTimes_length (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) :
    (recipeTimes recipes input state).length = recipes.length := by
  simp [recipeTimes]

@[simp] theorem recipeBlocks_get (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) :
    (recipeBlocks recipes input state).get
        ⟨index.val, by
          rw [recipeBlocks_length]
          exact index.isLt⟩ =
      tokenBlock input (state.actives.get index) (recipes.get index) := by
  simp [recipeBlocks]
  rfl

@[simp] theorem recipeTimes_get (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) :
    (recipeTimes recipes input state).get
        ⟨index.val, by
          rw [recipeTimes_length]
          exact index.isLt⟩ =
      recipeTime input (state.actives.get index) (recipes.get index) := by
  simp [recipeTimes]
  rfl

theorem recipeSuffixTokens_eq (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) :
    recipeSuffixTokens recipes input state index =
      tokenBlock input (state.actives.get index) (recipes.get index) ++
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTokens recipes input state
            ⟨index.val + 1, nextExists⟩
        else [] := by
  let blockIndex : Fin (recipeBlocks recipes input state).length :=
    ⟨index.val, by
      rw [recipeBlocks_length]
      exact index.isLt⟩
  unfold recipeSuffixTokens
  rw [← List.cons_get_drop_succ
    (l := recipeBlocks recipes input state) (n := blockIndex)]
  simp only [List.flatten_cons]
  rw [recipeBlocks_get]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists, blockIndex]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le (by simpa using beyond)]
    simp [nextExists]

theorem recipeSuffixTime_eq (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) :
    recipeSuffixTime recipes input state index =
      recipeTime input (state.actives.get index) (recipes.get index) +
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTime recipes input state
            ⟨index.val + 1, nextExists⟩
        else 0 := by
  let timeIndex : Fin (recipeTimes recipes input state).length :=
    ⟨index.val, by
      rw [recipeTimes_length]
      exact index.isLt⟩
  unfold recipeSuffixTime
  rw [← List.cons_get_drop_succ
    (l := recipeTimes recipes input state) (n := timeIndex)]
  simp only [List.sum_cons]
  rw [recipeTimes_get]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists, timeIndex]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le (by simpa using beyond)]
    simp [nextExists]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
