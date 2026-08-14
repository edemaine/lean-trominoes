/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerTemplate

/-!
# One complete inner position of the triangular emitter

One higher-position marker is removed from `remaining`, its possibly empty
inner template is emitted at the exact triangular position, and the marker is
recorded in `innerProcessed`.  Both the empty and nonempty template paths meet
the same restored invariant at `beginInner`.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

def beginInnerCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.beginInnerCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

end Parameters

theorem step_beginInner_cons_nonempty {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (nonempty : 0 < parameters.inner.length)
    (data : TapeData Data) (tail : List Unit)
    (remainingEq : data.remaining = () :: tail) :
    parameters.transition (parameters.beginInnerCfg data) =
      some (parameters.executeCfg .inner ⟨0, nonempty⟩
        { data with remaining := tail }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [Parameters.transition, Parameters.beginInnerCfg,
    Parameters.executeCfg, TM2.step, program, beginTemplate, nonempty,
    TriangularTemplateEmitterMachine.beginInnerCfg,
    TriangularTemplateEmitterMachine.executeCfg, cfg, tapes, stageCount,
    stageLabel]

theorem step_beginInner_cons_empty {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (empty : parameters.inner = [])
    (data : TapeData Data) (tail : List Unit)
    (remainingEq : data.remaining = () :: tail) :
    parameters.transition (parameters.beginInnerCfg data) =
      some (parameters.finishInnerPositionCfg
        { data with remaining := tail }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change inner = [] at empty
  subst inner
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [Parameters.transition, Parameters.beginInnerCfg,
    Parameters.finishInnerPositionCfg, TM2.step, program, beginTemplate,
    TriangularTemplateEmitterMachine.beginInnerCfg,
    TriangularTemplateEmitterMachine.finishInnerPositionCfg, cfg, tapes,
    stageCount, afterStage]

theorem step_finishInnerPosition {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data) :
    parameters.transition (parameters.finishInnerPositionCfg data) =
      some (parameters.beginInnerCfg
        { data with innerProcessed := () :: data.innerProcessed }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  simp [Parameters.transition, Parameters.finishInnerPositionCfg,
    Parameters.beginInnerCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.finishInnerPositionCfg,
    TriangularTemplateEmitterMachine.beginInnerCfg, cfg, tapes]

/-- Runtime of the whole inner template at one higher position. -/
def innerTemplateTime {Data : Type} (parameters : Parameters Data)
    (first outer innerCount : Nat) : Nat :=
  (parameters.inner.map (innerRecipeTime first outer innerCount)).sum

@[simp]
theorem innerRecipeSuffixTime_zero {Data : Type}
    (parameters : Parameters Data) (first outer innerCount : Nat) :
    innerRecipeSuffixTime parameters first outer innerCount 0 =
      innerTemplateTime parameters first outer innerCount := by
  simp [innerRecipeSuffixTime, innerTemplateTime]

@[simp]
theorem recipeSuffixTokens_inner_zero {Data : Type}
    (parameters : Parameters Data) (first position : Nat) :
    recipeSuffixTokens parameters .inner first position 0 =
      BivariateProgramTemplates.positionTokens parameters.inner first
        position := by
  simp [recipeSuffixTokens, stageRecipes,
    BivariateProgramTemplates.positionTokens]

/-- Execute one higher inner position, including template entry and exit. -/
def innerPosition_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (first outer innerCount : Nat)
    (tail : List Unit) (data : TapeData Data)
    (remainingEq : data.remaining = () :: tail)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate outer ())
    (innerEq : data.innerProcessed = List.replicate innerCount ())
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.beginInnerCfg data)
      (some (parameters.beginInnerCfg
        { data with
          first := List.replicate first ()
          remaining := tail
          processed := List.replicate outer ()
          innerProcessed := List.replicate (innerCount + 1) ()
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((BivariateProgramTemplates.positionTokens parameters.inner
                first (outer + 1 + innerCount)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (innerTemplateTime parameters first outer innerCount + 2) := by
  by_cases innerEmpty : parameters.inner = []
  · have entered := oneStep
      (step_beginInner_cons_empty parameters innerEmpty data tail remainingEq)
    let selectedData : TapeData Data := { data with remaining := tail }
    have finished := oneStep (step_finishInnerPosition parameters selectedData)
    have whole := EvalsToInTime.trans parameters.transition 1 1
      (parameters.beginInnerCfg data)
      (parameters.finishInnerPositionCfg selectedData)
      (some (parameters.beginInnerCfg
        { selectedData with
          innerProcessed := () :: selectedData.innerProcessed }))
      (by simpa [selectedData] using entered) finished
    convert whole using 1
    · simp [selectedData, innerEmpty, firstEq, processedEq, innerEq,
        firstScratchEq, positionScratchEq,
        BivariateProgramTemplates.positionTokens, List.replicate_succ]
    · simp [innerTemplateTime, innerEmpty]
  · have nonempty : 0 < parameters.inner.length := by
      cases innerEqList : parameters.inner with
      | nil => exact False.elim (innerEmpty innerEqList)
      | cons recipe recipes => simp
    let selectedData : TapeData Data := { data with remaining := tail }
    have entered := oneStep
      (step_beginInner_cons_nonempty parameters nonempty data tail remainingEq)
    have template := executeInnerRecipes_evalsInTime parameters
      ⟨0, nonempty⟩ first outer innerCount selectedData
      (by simpa [selectedData] using firstEq)
      (by simpa [selectedData] using processedEq)
      (by simpa [selectedData] using innerEq)
      (by simpa [selectedData] using firstScratchEq)
      (by simpa [selectedData] using positionScratchEq)
    let emittedData : TapeData Data :=
      { selectedData with
        first := List.replicate first ()
        processed := List.replicate outer ()
        innerProcessed := List.replicate innerCount ()
        firstScratch := []
        positionScratch := []
        outputReverse :=
          ((BivariateProgramTemplates.positionTokens parameters.inner first
              (outer + 1 + innerCount)).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              selectedData.outputReverse }
    have firstTwo := EvalsToInTime.trans parameters.transition 1
      (innerTemplateTime parameters first outer innerCount)
      (parameters.beginInnerCfg data)
      (parameters.executeCfg .inner ⟨0, nonempty⟩ selectedData)
      (some (parameters.finishInnerPositionCfg emittedData)) entered (by
        convert template using 1
        · rfl
        · simp [emittedData]
        · simp)
    have finished := oneStep (step_finishInnerPosition parameters emittedData)
    have whole := EvalsToInTime.trans parameters.transition
      (innerTemplateTime parameters first outer innerCount + 1) 1
      (parameters.beginInnerCfg data)
      (parameters.finishInnerPositionCfg emittedData)
      (some (parameters.beginInnerCfg
        { emittedData with
          innerProcessed := () :: emittedData.innerProcessed }))
      (by simpa using firstTwo) finished
    convert whole using 1
    · simp [emittedData, selectedData, List.replicate_succ]
    · omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
