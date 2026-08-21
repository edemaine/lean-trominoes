/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterRecipe

/-! # Recipe-list execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens
open TrivariateTemplateEmitter

def recipeSuffixTokens (recipes : List Recipe)
    (first second position : Nat) (index : Fin recipes.length) : List Token :=
  (recipes.drop index.val).flatMap
    (Recipe.tokens first second position)

theorem recipeSuffixTokens_eq (recipes : List Recipe)
    (first second position : Nat) (index : Fin recipes.length) :
    recipeSuffixTokens recipes first second position index =
      Recipe.tokens first second position (recipes.get index) ++
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTokens recipes first second position
            ⟨index.val + 1, nextExists⟩
        else [] := by
  unfold recipeSuffixTokens
  rw [← List.cons_get_drop_succ (l := recipes) (n := index)]
  simp only [List.flatMap_cons]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le beyond]
    simp [nextExists]

def recipeSuffixTime (recipes : List Recipe)
    (first second position : Nat) (index : Fin recipes.length) : Nat :=
  ((recipes.drop index.val).map
    (recipeTime first second position)).sum

theorem recipeSuffixTime_eq (recipes : List Recipe)
    (first second position : Nat) (index : Fin recipes.length) :
    recipeSuffixTime recipes first second position index =
      recipeTime first second position (recipes.get index) +
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTime recipes first second position
            ⟨index.val + 1, nextExists⟩
        else 0 := by
  unfold recipeSuffixTime
  rw [← List.cons_get_drop_succ (l := recipes) (n := index)]
  simp only [List.map_cons, List.sum_cons]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le beyond]
    simp [nextExists]

def executeRecipes_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (first second position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (secondEq : data.second = List.replicate second ())
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (executeCfg index data)
      (some (beginPositionCfg
        { data with
          first := List.replicate first ()
          second := List.replicate second ()
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes first second position index).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeSuffixTime recipes first second position index) := by
  have current := executeRecipe_evalsInTime firstSelected secondSelected
    positionSelected recipes ending index first second position data
    firstEq secondEq processedEq scratchEq
  by_cases nextExists : index.val + 1 < recipes.length
  · let nextIndex : Fin recipes.length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        first := List.replicate first ()
        second := List.replicate second ()
        processed := List.replicate position ()
        scratch := []
        outputReverse :=
          ((Recipe.tokens first second position (recipes.get index)).map
            fun token => (Sum.inr token : Workspace Data)).reverse ++
              data.outputReverse }
    have first' : EvalsToInTime
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (executeCfg index data) (some (executeCfg nextIndex currentData))
        (recipeTime first second position (recipes.get index)) := by
      convert current using 1
      simp [afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := executeRecipes_evalsInTime firstSelected secondSelected
      positionSelected recipes ending nextIndex first second position
      currentData rfl rfl rfl rfl
    have composed := EvalsToInTime.trans
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (recipeTime first second position (recipes.get index))
      (recipeSuffixTime recipes first second position nextIndex)
      (executeCfg index data) (executeCfg nextIndex currentData)
      (some (beginPositionCfg
        { currentData with
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes first second position nextIndex).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                currentData.outputReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, nextIndex, currentData, List.map_append,
        List.reverse_append, List.append_assoc]
    · rw [recipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        (executeCfg index data)
        (some (beginPositionCfg
          { data with
            first := List.replicate first ()
            second := List.replicate second ()
            processed := () :: List.replicate position ()
            scratch := []
            outputReverse :=
              ((Recipe.tokens first second position
                  (recipes.get index)).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  data.outputReverse }))
        (recipeTime first second position (recipes.get index)) := by
      convert current using 1
      simp [afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [recipeSuffixTime_eq]
      simp [nextExists]
termination_by recipes.length - index.val
decreasing_by omega

def templateTime (recipes : List Recipe)
    (first second position : Nat) : Nat :=
  (recipes.map (recipeTime first second position)).sum

@[simp] theorem recipeSuffixTokens_zero (recipes : List Recipe)
    (first second position : Nat) (nonempty : 0 < recipes.length) :
    recipeSuffixTokens recipes first second position ⟨0, nonempty⟩ =
      positionTokens recipes first second position := by
  simp [recipeSuffixTokens, positionTokens]

@[simp] theorem recipeSuffixTime_zero (recipes : List Recipe)
    (first second position : Nat) (nonempty : 0 < recipes.length) :
    recipeSuffixTime recipes first second position ⟨0, nonempty⟩ =
      templateTime recipes first second position := by
  simp [recipeSuffixTime, templateTime]

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
