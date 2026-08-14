/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterRecipe

/-!
# Complete outer-template execution of the triangular emitter

The exact one-recipe execution theorem is lifted over either non-inner recipe
list.  The resulting run emits the complete remaining template suffix in
order, restores all persistent counters and scratch stacks after every recipe,
and reaches the stage continuation with an explicit additive runtime.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

/-- Tokens contributed by the unexecuted suffix of one stage template. -/
def recipeSuffixTokens {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (first position index : Nat) : List Token :=
  ((stageRecipes parameters.outerFirst parameters.inner
      parameters.outerSecond stage).drop index).flatMap
    (BivariateProgramTemplates.Recipe.tokens first position)

theorem recipeSuffixTokens_eq {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (first position : Nat)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) :
    recipeSuffixTokens parameters stage first position index.val =
      BivariateProgramTemplates.Recipe.tokens first position
          (recipeAt parameters.outerFirst parameters.inner
            parameters.outerSecond stage index) ++
        if _nextExists : index.val + 1 <
            stageCount parameters.outerFirst parameters.inner
              parameters.outerSecond stage then
          recipeSuffixTokens parameters stage first position (index.val + 1)
        else [] := by
  cases stage with
  | outerFirst =>
      unfold recipeSuffixTokens
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.outerFirst) (n := index)]
      simp only [List.flatMap_cons]
      by_cases nextExists : index.val + 1 < parameters.outerFirst.length
      · simp [nextExists]
      · have beyond : parameters.outerFirst.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]
  | inner =>
      unfold recipeSuffixTokens
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.inner) (n := index)]
      simp only [List.flatMap_cons]
      by_cases nextExists : index.val + 1 < parameters.inner.length
      · simp [nextExists]
      · have beyond : parameters.inner.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]
  | outerSecond =>
      unfold recipeSuffixTokens
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.outerSecond) (n := index)]
      simp only [List.flatMap_cons]
      by_cases nextExists : index.val + 1 < parameters.outerSecond.length
      · simp [nextExists]
      · have beyond : parameters.outerSecond.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]

/-- Runtime of the unexecuted suffix of one non-inner stage template. -/
def outerRecipeSuffixTime {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (first position index : Nat) : Nat :=
  (((stageRecipes parameters.outerFirst parameters.inner
      parameters.outerSecond stage).drop index).map
        (outerRecipeTime first position)).sum

theorem outerRecipeSuffixTime_eq {Data : Type}
    (parameters : Parameters Data) (stage : Stage) (first position : Nat)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) :
    outerRecipeSuffixTime parameters stage first position index.val =
      outerRecipeTime first position
          (recipeAt parameters.outerFirst parameters.inner
            parameters.outerSecond stage index) +
        if _nextExists : index.val + 1 <
            stageCount parameters.outerFirst parameters.inner
              parameters.outerSecond stage then
          outerRecipeSuffixTime parameters stage first position
            (index.val + 1)
        else 0 := by
  cases stage with
  | outerFirst =>
      unfold outerRecipeSuffixTime
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.outerFirst) (n := index)]
      simp only [List.map_cons, List.sum_cons]
      by_cases nextExists : index.val + 1 < parameters.outerFirst.length
      · simp [nextExists]
      · have beyond : parameters.outerFirst.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]
  | inner =>
      unfold outerRecipeSuffixTime
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.inner) (n := index)]
      simp only [List.map_cons, List.sum_cons]
      by_cases nextExists : index.val + 1 < parameters.inner.length
      · simp [nextExists]
      · have beyond : parameters.inner.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]
  | outerSecond =>
      unfold outerRecipeSuffixTime
      simp only [stageRecipes, stageCount, recipeAt]
      rw [← List.cons_get_drop_succ (l := parameters.outerSecond) (n := index)]
      simp only [List.map_cons, List.sum_cons]
      by_cases nextExists : index.val + 1 < parameters.outerSecond.length
      · simp [nextExists]
      · have beyond : parameters.outerSecond.length ≤ index.val + 1 := by omega
        rw [List.drop_eq_nil_of_le beyond]
        simp [nextExists]

/-- Execute the complete remaining suffix of either outer-stage template. -/
def executeOuterRecipes_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (notInner : stage.isInner = false)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (first position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate position ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.executeCfg stage index data)
      (some (cfg
        (afterStage parameters.outerFirst parameters.inner
          parameters.outerSecond stage) none
        { data with
          first := List.replicate first ()
          processed := List.replicate position ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((recipeSuffixTokens parameters stage first position
                index.val).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (outerRecipeSuffixTime parameters stage first position index.val) := by
  have current := executeOuterRecipe_evalsInTime parameters stage notInner
    index first position data firstEq processedEq firstScratchEq
      positionScratchEq
  by_cases nextExists : index.val + 1 <
      stageCount parameters.outerFirst parameters.inner
        parameters.outerSecond stage
  · let nextIndex : Fin (stageCount parameters.outerFirst parameters.inner
        parameters.outerSecond stage) :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        first := List.replicate first ()
        processed := List.replicate position ()
        firstScratch := []
        positionScratch := []
        outputReverse :=
          ((BivariateProgramTemplates.Recipe.tokens first position
              (recipeAt parameters.outerFirst parameters.inner
                parameters.outerSecond stage index)).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              data.outputReverse }
    have first' : EvalsToInTime parameters.transition
        (parameters.executeCfg stage index data)
        (some (parameters.executeCfg stage nextIndex currentData))
        (outerRecipeTime first position
          (recipeAt parameters.outerFirst parameters.inner
            parameters.outerSecond stage index)) := by
      convert current using 1
      simp [Parameters.afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := executeOuterRecipes_evalsInTime parameters stage notInner
      nextIndex first position currentData rfl rfl rfl rfl
    have composed := EvalsToInTime.trans parameters.transition
      (outerRecipeTime first position
        (recipeAt parameters.outerFirst parameters.inner
          parameters.outerSecond stage index))
      (outerRecipeSuffixTime parameters stage first position nextIndex.val)
      (parameters.executeCfg stage index data)
      (parameters.executeCfg stage nextIndex currentData)
      (some (cfg
        (afterStage parameters.outerFirst parameters.inner
          parameters.outerSecond stage) none
        { currentData with
          first := List.replicate first ()
          processed := List.replicate position ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((recipeSuffixTokens parameters stage first position
                nextIndex.val).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                currentData.outputReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, nextIndex, currentData, List.map_append,
        List.reverse_append, List.append_assoc]
    · rw [outerRecipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime parameters.transition
        (parameters.executeCfg stage index data)
        (some (cfg
          (afterStage parameters.outerFirst parameters.inner
            parameters.outerSecond stage) none
          { data with
            first := List.replicate first ()
            processed := List.replicate position ()
            firstScratch := []
            positionScratch := []
            outputReverse :=
              ((BivariateProgramTemplates.Recipe.tokens first position
                  (recipeAt parameters.outerFirst parameters.inner
                    parameters.outerSecond stage index)).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  data.outputReverse }))
        (outerRecipeTime first position
          (recipeAt parameters.outerFirst parameters.inner
            parameters.outerSecond stage index)) := by
      convert current using 1
      simp [Parameters.afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [outerRecipeSuffixTime_eq]
      simp [nextExists]
termination_by
  stageCount parameters.outerFirst parameters.inner parameters.outerSecond
    stage - index.val
decreasing_by omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
