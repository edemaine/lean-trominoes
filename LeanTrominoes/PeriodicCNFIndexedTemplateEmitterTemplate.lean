/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterRecipe

/-!
# Complete indexed item-template execution

Lift exact recipe execution through the suffix of one selected item's finite
recipe list.  The last recipe advances the selected-position counter once and
returns to the input scan.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

def recipeSuffixTokens (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) : List Token :=
  (recipes.drop index.val).flatMap (Recipe.tokens position)

theorem recipeSuffixTokens_eq (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTokens recipes position index =
      Recipe.tokens position (recipes.get index) ++
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTokens recipes position
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

def recipeSuffixTime (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) : Nat :=
  ((recipes.drop index.val).map (recipeTime position)).sum

theorem recipeSuffixTime_eq (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTime recipes position index =
      recipeTime position (recipes.get index) +
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTime recipes position
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
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (position : Nat)
    (data : TapeData Data)
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program family))
      (executeCfg item index data)
      (some (scanCfg (family := family)
        { data with
          processed := () :: List.replicate position ()
          scratch := []
          tokenReverse :=
            (recipeSuffixTokens (recipesFor family item) position index).reverse ++
              data.tokenReverse }))
      (recipeSuffixTime (recipesFor family item) position index) := by
  have first := executeRecipe_evalsInTime family item index position data
    processedEq scratchEq
  by_cases nextExists : index.val + 1 < (recipesFor family item).length
  · let nextIndex : Fin (recipesFor family item).length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        processed := List.replicate position ()
        scratch := []
        tokenReverse :=
          (Recipe.tokens position
            ((recipesFor family item).get index)).reverse ++
              data.tokenReverse }
    have first' : EvalsToInTime
        (TM2.step (program family))
        (executeCfg item index data)
        (some (executeCfg item nextIndex currentData))
        (recipeTime position ((recipesFor family item).get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := executeRecipes_evalsInTime family item nextIndex position
      currentData rfl rfl
    have composed := EvalsToInTime.trans
      (TM2.step (program family))
      (recipeTime position ((recipesFor family item).get index))
      (recipeSuffixTime (recipesFor family item) position nextIndex)
      (executeCfg item index data) (executeCfg item nextIndex currentData)
      (some (scanCfg (family := family)
        { currentData with
          processed := () :: List.replicate position ()
          scratch := []
          tokenReverse :=
            (recipeSuffixTokens (recipesFor family item) position
              nextIndex).reverse ++ currentData.tokenReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, nextIndex, currentData, List.reverse_append,
        List.append_assoc]
    · rw [recipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime
        (TM2.step (program family))
        (executeCfg item index data)
        (some (scanCfg (family := family)
          { data with
            processed := () :: List.replicate position ()
            scratch := []
            tokenReverse :=
              (Recipe.tokens position
                ((recipesFor family item).get index)).reverse ++
                  data.tokenReverse }))
        (recipeTime position ((recipesFor family item).get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [recipeSuffixTime_eq]
      simp [nextExists]
termination_by (recipesFor family item).length - index.val
decreasing_by omega

def templateTime (recipes : List Recipe) (position : Nat) : Nat :=
  (recipes.map (recipeTime position)).sum

@[simp]
theorem recipeSuffixTokens_zero (recipes : List Recipe) (position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTokens recipes position ⟨0, nonempty⟩ =
      positionTokens recipes position := by
  simp [recipeSuffixTokens, positionTokens]

@[simp]
theorem recipeSuffixTime_zero (recipes : List Recipe) (position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTime recipes position ⟨0, nonempty⟩ =
      templateTime recipes position := by
  simp [recipeSuffixTime, templateTime]

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
