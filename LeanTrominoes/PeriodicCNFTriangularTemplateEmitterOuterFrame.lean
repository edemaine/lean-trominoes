/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterStage

/-!
# One complete outer frame of the triangular emitter

The outer-first template, all strictly higher inner templates, the inner fold,
and the outer-second template are composed with the two frame-control steps.
The exact output is the semantic `frameTokens` block, one outer marker moves
from `remaining` through `current` to `processed`, and every scratch invariant
is restored.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

theorem outerSecondStartCfg_eq_outerStageStartCfg {Data : Type}
    (parameters : Parameters Data) (data : TapeData Data) :
    parameters.outerSecondStartCfg data =
      parameters.outerStageStartCfg .outerSecond data := by
  unfold Parameters.outerSecondStartCfg Parameters.outerStageStartCfg
  split <;>
    simp_all [stageCount, afterStage, Parameters.finishOuterCfg,
      TriangularTemplateEmitterMachine.finishOuterCfg]

theorem step_beginOuter_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    parameters.transition (parameters.beginOuterCfg data) =
      some (parameters.outerStageStartCfg .outerFirst
        { data with
          remaining := tail
          current := () :: data.current }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [Parameters.transition, Parameters.beginOuterCfg,
    Parameters.outerStageStartCfg, Parameters.executeCfg,
    TM2.step, program, beginTemplate,
    TriangularTemplateEmitterMachine.beginOuterCfg,
    TriangularTemplateEmitterMachine.executeCfg, cfg, tapes, stageCount,
    stageLabel, afterStage]
  split <;> simp_all

theorem step_finishOuter_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (tail : List Unit) (currentEq : data.current = () :: tail) :
    parameters.transition (parameters.finishOuterCfg data) =
      some (parameters.beginOuterCfg
        { data with
          current := tail
          processed := () :: data.processed }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change current = () :: tail at currentEq
  subst current
  simp [Parameters.transition, Parameters.finishOuterCfg,
    Parameters.beginOuterCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.finishOuterCfg,
    TriangularTemplateEmitterMachine.beginOuterCfg, cfg, tapes]

/-- Exact runtime of one outer frame with `higherCount` later positions. -/
def outerFrameTime {Data : Type} (parameters : Parameters Data)
    (first position higherCount : Nat) : Nat :=
  outerTemplateTime parameters .outerFirst first position +
    innerPositionRangeTime parameters first position 0 higherCount +
    (higherCount + 2) +
    outerTemplateTime parameters .outerSecond first position + 2

/-- Execute one complete outer frame and return to the outer loop. -/
def outerFrame_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (first position higherCount : Nat)
    (data : TapeData Data)
    (remainingEq :
      data.remaining = List.replicate (higherCount + 1) ())
    (firstEq : data.first = List.replicate first ())
    (currentEq : data.current = [])
    (processedEq : data.processed = List.replicate position ())
    (innerEq : data.innerProcessed = [])
    (firstScratchEq : data.firstScratch = [])
    (positionScratchEq : data.positionScratch = []) :
    EvalsToInTime parameters.transition
      (parameters.beginOuterCfg data)
      (some (parameters.beginOuterCfg
        { data with
          first := List.replicate first ()
          remaining := List.replicate higherCount ()
          current := []
          processed := List.replicate (position + 1) ()
          innerProcessed := []
          firstScratch := []
          positionScratch := []
          outputReverse :=
            ((frameTokens parameters.outerFirst parameters.inner
                parameters.outerSecond parameters.innerBase
                parameters.innerCloser parameters.frameCloser first position
                higherCount).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (outerFrameTime parameters first position higherCount) := by
  let selectedData : TapeData Data :=
    { data with
      remaining := List.replicate higherCount ()
      current := [()] }
  have entered := oneStep
    (step_beginOuter_cons parameters data (List.replicate higherCount ()) (by
      simpa [List.replicate_succ] using remainingEq))
  have outerFirstRun := executeOuterTemplate_evalsInTime parameters
    .outerFirst rfl first position selectedData
    (by simpa [selectedData] using firstEq)
    (by simpa [selectedData] using processedEq)
    (by simpa [selectedData] using firstScratchEq)
    (by simpa [selectedData] using positionScratchEq)
  let outerFirstData : TapeData Data :=
    { selectedData with
      first := List.replicate first ()
      processed := List.replicate position ()
      firstScratch := []
      positionScratch := []
      outputReverse :=
        ((BivariateProgramTemplates.positionTokens parameters.outerFirst first
            position).map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++
            selectedData.outputReverse }
  have throughOuterFirst := EvalsToInTime.trans parameters.transition 1
    (outerTemplateTime parameters .outerFirst first position)
    (parameters.beginOuterCfg data)
    (parameters.outerStageStartCfg .outerFirst selectedData)
    (some (parameters.beginInnerCfg outerFirstData))
    (by simpa [selectedData, currentEq] using entered) (by
      simpa [outerFirstData, Parameters.beginInnerCfg,
        TriangularTemplateEmitterMachine.beginInnerCfg, afterStage,
        stageRecipes] using outerFirstRun)
  have innerRangeRun := innerPositions_evalsInTime parameters first position 0
    higherCount outerFirstData (by simp [outerFirstData, selectedData])
    rfl rfl (by simp [outerFirstData, selectedData, innerEq]) rfl rfl
  let innerRangeData : TapeData Data :=
    { outerFirstData with
      first := List.replicate first ()
      remaining := []
      processed := List.replicate position ()
      innerProcessed := List.replicate higherCount ()
      firstScratch := []
      positionScratch := []
      outputReverse :=
        ((BivariateTemplateEmitterMachine.positionRangeTokens
            parameters.inner first (position + 1) higherCount).map
          fun token => (Sum.inr token : Workspace Data)).reverse ++
            outerFirstData.outputReverse }
  have throughInnerRange := EvalsToInTime.trans parameters.transition
    (outerTemplateTime parameters .outerFirst first position + 1)
    (innerPositionRangeTime parameters first position 0 higherCount)
    (parameters.beginOuterCfg data)
    (parameters.beginInnerCfg outerFirstData)
    (some (parameters.beginInnerCfg innerRangeData))
    throughOuterFirst (by
        simpa [innerRangeData] using innerRangeRun)
  have folded := finishInnerFold_evalsInTime parameters higherCount
    innerRangeData rfl rfl
  let foldedData : TapeData Data :=
    { innerRangeData with
      remaining := List.replicate higherCount ()
      innerProcessed := []
      outputReverse :=
        ((parameters.innerBase ++
            repeatTokens parameters.innerCloser higherCount ++
            parameters.frameCloser).map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++
            innerRangeData.outputReverse }
  have throughFold := EvalsToInTime.trans parameters.transition
    (innerPositionRangeTime parameters first position 0 higherCount +
      (outerTemplateTime parameters .outerFirst first position + 1))
    (higherCount + 2)
    (parameters.beginOuterCfg data)
    (parameters.beginInnerCfg innerRangeData)
    (some (parameters.outerStageStartCfg .outerSecond foldedData))
    throughInnerRange (by
      rw [← outerSecondStartCfg_eq_outerStageStartCfg]
      simpa [foldedData] using folded)
  have outerSecondRun := executeOuterTemplate_evalsInTime parameters
    .outerSecond rfl first position foldedData rfl rfl rfl rfl
  let outerSecondData : TapeData Data :=
    { foldedData with
      first := List.replicate first ()
      processed := List.replicate position ()
      firstScratch := []
      positionScratch := []
      outputReverse :=
        ((BivariateProgramTemplates.positionTokens parameters.outerSecond first
            position).map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++
            foldedData.outputReverse }
  have throughOuterSecond := EvalsToInTime.trans parameters.transition
    (higherCount + 2 +
      (innerPositionRangeTime parameters first position 0 higherCount +
        (outerTemplateTime parameters .outerFirst first position + 1)))
    (outerTemplateTime parameters .outerSecond first position)
    (parameters.beginOuterCfg data)
    (parameters.outerStageStartCfg .outerSecond foldedData)
    (some (parameters.finishOuterCfg outerSecondData))
    throughFold (by
      simpa [outerSecondData, Parameters.finishOuterCfg,
        TriangularTemplateEmitterMachine.finishOuterCfg, afterStage,
        stageRecipes] using outerSecondRun)
  have finished := oneStep
    (step_finishOuter_cons parameters outerSecondData [] (by
      simp [outerSecondData, foldedData, innerRangeData, outerFirstData,
        selectedData]))
  have whole := EvalsToInTime.trans parameters.transition
    (outerTemplateTime parameters .outerSecond first position +
      (higherCount + 2 +
        (innerPositionRangeTime parameters first position 0 higherCount +
          (outerTemplateTime parameters .outerFirst first position + 1))))
    1
    (parameters.beginOuterCfg data)
    (parameters.finishOuterCfg outerSecondData)
    (some (parameters.beginOuterCfg
      { outerSecondData with
        current := []
        processed := () :: outerSecondData.processed }))
    throughOuterSecond finished
  convert whole using 1
  · simp [outerSecondData, foldedData, innerRangeData, outerFirstData,
      selectedData, frameTokens, List.map_append, List.reverse_append,
      List.append_assoc, List.replicate_succ]
  · simp [outerFrameTime]
    omega

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
