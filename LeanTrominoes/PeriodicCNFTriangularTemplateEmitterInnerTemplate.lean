/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterTemplate
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerRecipe

/-!
# Complete inner-template execution of the triangular emitter

The exact three-counter recipe theorem is lifted over the inner recipe list.
Every recipe uses the same semantic position `outer + 1 + inner`, all counters
and scratch stacks are restored between recipes, and the complete template
reaches the finished-inner-position continuation.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

def finishInnerPositionCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.finishInnerPositionCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

end Parameters

/-- Runtime of the unexecuted suffix of the inner-stage template. -/
def innerRecipeSuffixTime {Data : Type} (parameters : Parameters Data)
    (first outer innerCount index : Nat) : Nat :=
  ((parameters.inner.drop index).map
    (innerRecipeTime first outer innerCount)).sum

theorem innerRecipeSuffixTime_eq {Data : Type}
    (parameters : Parameters Data) (first outer innerCount : Nat)
    (index : Fin parameters.inner.length) :
    innerRecipeSuffixTime parameters first outer innerCount index.val =
      innerRecipeTime first outer innerCount (parameters.inner.get index) +
        if _nextExists : index.val + 1 < parameters.inner.length then
          innerRecipeSuffixTime parameters first outer innerCount
            (index.val + 1)
        else 0 := by
  unfold innerRecipeSuffixTime
  rw [← List.cons_get_drop_succ (l := parameters.inner) (n := index)]
  simp only [List.map_cons, List.sum_cons]
  by_cases nextExists : index.val + 1 < parameters.inner.length
  · simp [nextExists]
  · have beyond : parameters.inner.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le beyond]
    simp [nextExists]

/-- Execute the complete remaining suffix of the inner-stage template. -/
def executeInnerRecipes_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (first outer innerCount : Nat) (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate outer ())
    (innerEq : data.innerProcessed = List.replicate innerCount ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.executeCfg .inner index data)
      (some (parameters.finishInnerPositionCfg
        { data with
          first := List.replicate first ()
          processed := List.replicate outer ()
          innerProcessed := List.replicate innerCount ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((recipeSuffixTokens parameters .inner first
                (outer + 1 + innerCount) index.val).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (innerRecipeSuffixTime parameters first outer innerCount index.val) := by
  have current := executeInnerRecipe_evalsInTime parameters index first outer
    innerCount data firstEq processedEq innerEq firstScratchEq
      positionScratchEq
  by_cases nextExists : index.val + 1 < parameters.inner.length
  · let nextIndex : Fin parameters.inner.length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        first := List.replicate first ()
        processed := List.replicate outer ()
        innerProcessed := List.replicate innerCount ()
        firstScratch := []
        positionScratch := []
        outputReverse :=
          ((BivariateProgramTemplates.Recipe.tokens first
              (outer + 1 + innerCount)
              (parameters.inner.get index)).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              data.outputReverse }
    have first' : EvalsToInTime parameters.transition
        (parameters.executeCfg .inner index data)
        (some (parameters.executeCfg .inner nextIndex currentData))
        (innerRecipeTime first outer innerCount
          (parameters.inner.get index)) := by
      convert current using 1
      simp [Parameters.afterRecipeCfg, stageCount, nextExists, nextIndex,
        currentData]
    have rest := executeInnerRecipes_evalsInTime parameters nextIndex first
      outer innerCount currentData rfl rfl rfl rfl rfl
    have composed := EvalsToInTime.trans parameters.transition
      (innerRecipeTime first outer innerCount (parameters.inner.get index))
      (innerRecipeSuffixTime parameters first outer innerCount nextIndex.val)
      (parameters.executeCfg .inner index data)
      (parameters.executeCfg .inner nextIndex currentData)
      (some (parameters.finishInnerPositionCfg
        { currentData with
          first := List.replicate first ()
          processed := List.replicate outer ()
          innerProcessed := List.replicate innerCount ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((recipeSuffixTokens parameters .inner first
                (outer + 1 + innerCount) nextIndex.val).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                currentData.outputReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [stageCount, recipeAt, stageRecipes, nextExists, nextIndex,
        currentData, List.map_append, List.reverse_append,
        List.append_assoc]
    · rw [innerRecipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime parameters.transition
        (parameters.executeCfg .inner index data)
        (some (parameters.finishInnerPositionCfg
          { data with
            first := List.replicate first ()
            processed := List.replicate outer ()
            innerProcessed := List.replicate innerCount ()
            firstScratch := []
            positionScratch := []
            outputReverse :=
              ((BivariateProgramTemplates.Recipe.tokens first
                  (outer + 1 + innerCount)
                  (parameters.inner.get index)).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  data.outputReverse }))
        (innerRecipeTime first outer innerCount
          (parameters.inner.get index)) := by
      convert current using 1
      simp [Parameters.afterRecipeCfg, nextExists,
        Parameters.finishInnerPositionCfg,
        TriangularTemplateEmitterMachine.finishInnerPositionCfg,
        afterStage, stageCount]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, stageCount, recipeAt, stageRecipes]
    · rw [innerRecipeSuffixTime_eq]
      simp [nextExists]
termination_by parameters.inner.length - index.val
decreasing_by omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
