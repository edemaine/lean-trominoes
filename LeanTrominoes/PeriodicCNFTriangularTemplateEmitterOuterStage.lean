/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerFold

/-!
# Complete non-inner stage templates of the triangular emitter

This file packages the common possibly empty entry convention for the two
outer templates.  From that entry, either a zero-step empty run or the verified
recipe-list run reaches the stage continuation with exact full-template tokens
and runtime.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

/-- Configuration selected by the possibly empty recipe list of one stage. -/
def outerStageStartCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (data : TapeData Data) :=
  if nonempty : 0 < stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage then
    parameters.executeCfg stage ⟨0, nonempty⟩ data
  else
    cfg (afterStage parameters.outerFirst parameters.inner
      parameters.outerSecond stage) none data

end Parameters

/-- Runtime of a complete non-inner template. -/
def outerTemplateTime {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (first position : Nat) : Nat :=
  ((stageRecipes parameters.outerFirst parameters.inner
      parameters.outerSecond stage).map
    (outerRecipeTime first position)).sum

@[simp]
theorem outerRecipeSuffixTime_zero {Data : Type}
    (parameters : Parameters Data) (stage : Stage)
    (first position : Nat) :
    outerRecipeSuffixTime parameters stage first position 0 =
      outerTemplateTime parameters stage first position := by
  simp [outerRecipeSuffixTime, outerTemplateTime]

@[simp]
theorem recipeSuffixTokens_zero {Data : Type}
    (parameters : Parameters Data) (stage : Stage)
    (first position : Nat) :
    recipeSuffixTokens parameters stage first position 0 =
      BivariateProgramTemplates.positionTokens
        (stageRecipes parameters.outerFirst parameters.inner
          parameters.outerSecond stage) first position := by
  simp [recipeSuffixTokens, BivariateProgramTemplates.positionTokens]

/-- Execute a complete possibly empty non-inner template. -/
def executeOuterTemplate_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (notInner : stage.isInner = false) (first position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate position ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.outerStageStartCfg stage data)
      (some (cfg
        (afterStage parameters.outerFirst parameters.inner
          parameters.outerSecond stage) none
        { data with
          first := List.replicate first ()
          processed := List.replicate position ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateProgramTemplates.positionTokens
                (stageRecipes parameters.outerFirst parameters.inner
                  parameters.outerSecond stage) first position).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (outerTemplateTime parameters stage first position) := by
  by_cases nonempty : 0 < stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage
  · have run := executeOuterRecipes_evalsInTime parameters stage notInner
      ⟨0, nonempty⟩ first position data firstEq processedEq firstScratchEq
        positionScratchEq
    convert run using 1
    · simp [Parameters.outerStageStartCfg, nonempty]
    · simp
    · simp
  · have stageEmpty :
        stageRecipes parameters.outerFirst parameters.inner
          parameters.outerSecond stage = [] := by
      cases stage <;>
        simp_all [stageRecipes, stageCount, List.length_eq_zero_iff]
    have run := EvalsToInTime.refl parameters.transition
      (cfg (afterStage parameters.outerFirst parameters.inner
        parameters.outerSecond stage) none data)
    convert run using 1
    · simp [Parameters.outerStageStartCfg, nonempty]
    · congr 2
      cases data
      simp_all [BivariateProgramTemplates.positionTokens]
    · simp [outerTemplateTime, stageEmpty]

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
