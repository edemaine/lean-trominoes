/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerRange

/-!
# Inner-fold restoration of the triangular emitter

After all strictly higher templates have been emitted, the machine emits the
inner base, restores every processed higher marker to `remaining` while
emitting one closer, emits the frame closer, and enters the possibly empty
outer-second template.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

namespace Parameters

def restoreInnerRangeCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.restoreInnerRangeCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

def finishOuterCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.finishOuterCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

/-- Configuration selected by the possibly empty outer-second template. -/
def outerSecondStartCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  if nonempty : 0 < parameters.outerSecond.length then
    parameters.executeCfg .outerSecond ⟨0, nonempty⟩ data
  else
    parameters.finishOuterCfg data

end Parameters

theorem step_beginInner_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (remainingEq : data.remaining = []) :
    parameters.transition (parameters.beginInnerCfg data) =
      some (parameters.restoreInnerRangeCfg
        { data with
          remaining := []
          outputReverse :=
            (parameters.innerBase.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change remaining = [] at remainingEq
  subst remaining
  simp [Parameters.transition, Parameters.beginInnerCfg,
    Parameters.restoreInnerRangeCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.beginInnerCfg,
    TriangularTemplateEmitterMachine.restoreInnerRangeCfg, cfg, tapes,
    stepAux_pushTokens]

theorem step_restoreInnerRange_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (tail : List Unit)
    (innerEq : data.innerProcessed = () :: tail) :
    parameters.transition (parameters.restoreInnerRangeCfg data) =
      some (parameters.restoreInnerRangeCfg
        { data with
          remaining := () :: data.remaining
          innerProcessed := tail
          outputReverse :=
            (parameters.innerCloser.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change innerProcessed = () :: tail at innerEq
  subst innerProcessed
  simp [Parameters.transition, Parameters.restoreInnerRangeCfg,
    TM2.step, program,
    TriangularTemplateEmitterMachine.restoreInnerRangeCfg, cfg, tapes,
    stepAux_pushTokens]

theorem step_restoreInnerRange_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (innerEq : data.innerProcessed = []) :
    parameters.transition (parameters.restoreInnerRangeCfg data) =
      some (parameters.outerSecondStartCfg
        { data with
          innerProcessed := []
          outputReverse :=
            (parameters.frameCloser.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change innerProcessed = [] at innerEq
  subst innerProcessed
  simp [Parameters.transition, Parameters.restoreInnerRangeCfg,
    Parameters.outerSecondStartCfg, Parameters.finishOuterCfg,
    Parameters.executeCfg, TM2.step, program, beginTemplate,
    TriangularTemplateEmitterMachine.restoreInnerRangeCfg,
    TriangularTemplateEmitterMachine.finishOuterCfg,
    TriangularTemplateEmitterMachine.executeCfg, cfg, tapes,
    stepAux_pushTokens, stageCount, stageLabel, afterStage]
  split <;> simp_all

/-- Restore the complete higher range and emit its closers plus the frame
closer. -/
def restoreInnerRange_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (count : Nat) (data : TapeData Data)
    (innerEq : data.innerProcessed = List.replicate count ()) :
    EvalsToInTime parameters.transition
      (parameters.restoreInnerRangeCfg data)
      (some (parameters.outerSecondStartCfg
        { data with
          remaining := List.replicate count () ++ data.remaining
          innerProcessed := []
          outputReverse :=
            ((repeatTokens parameters.innerCloser count ++
                parameters.frameCloser).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := oneStep
        (step_restoreInnerRange_nil parameters data (by simpa using innerEq))
      convert step using 1
      all_goals simp [repeatTokens]
  | succ count induction =>
      let nextData : TapeData Data :=
        { data with
          remaining := () :: data.remaining
          innerProcessed := List.replicate count ()
          outputReverse :=
            (parameters.innerCloser.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }
      have firstStep := oneStep
        (step_restoreInnerRange_cons parameters data
          (List.replicate count ()) (by
            simpa [List.replicate_succ] using innerEq))
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition 1
        (count + 1)
        (parameters.restoreInnerRangeCfg data)
        (parameters.restoreInnerRangeCfg nextData)
        (some (parameters.outerSecondStartCfg
          { nextData with
            remaining :=
              List.replicate count () ++ nextData.remaining
            innerProcessed := []
            outputReverse :=
              ((repeatTokens parameters.innerCloser count ++
                  parameters.frameCloser).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  nextData.outputReverse }))
        (by simpa [nextData] using firstStep) rest
      convert composed using 1
      · simp [nextData, repeatTokens, List.map_append,
          List.reverse_append, List.append_assoc, List.replicate_succ]
        have remainingOrder :
            () :: (List.replicate count () ++ data.remaining) =
              List.replicate count () ++ () :: data.remaining := by
          calc
            () :: (List.replicate count () ++ data.remaining) =
                (() :: List.replicate count ()) ++ data.remaining := rfl
            _ = List.replicate (count + 1) () ++ data.remaining := by
              rw [List.replicate_succ]
            _ = (List.replicate count () ++ [()]) ++ data.remaining := by
              rw [replicate_unit_add_one_right]
            _ = List.replicate count () ++ () :: data.remaining := by
              simp [List.append_assoc]
        rw [remainingOrder]

/-- Emit and close the complete inner fold after all higher templates. -/
def finishInnerFold_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (count : Nat) (data : TapeData Data)
    (remainingEq : data.remaining = [])
    (innerEq : data.innerProcessed = List.replicate count ()) :
    EvalsToInTime parameters.transition
      (parameters.beginInnerCfg data)
      (some (parameters.outerSecondStartCfg
        { data with
          remaining := List.replicate count ()
          innerProcessed := []
          outputReverse :=
            ((parameters.innerBase ++
                repeatTokens parameters.innerCloser count ++
                parameters.frameCloser).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (count + 2) := by
  let basedData : TapeData Data :=
    { data with
      remaining := []
      outputReverse :=
        (parameters.innerBase.map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++
            data.outputReverse }
  have based := oneStep
    (step_beginInner_nil parameters data remainingEq)
  have restored := restoreInnerRange_evalsInTime parameters count basedData
    (by simpa [basedData] using innerEq)
  have whole := EvalsToInTime.trans parameters.transition 1 (count + 1)
    (parameters.beginInnerCfg data)
    (parameters.restoreInnerRangeCfg basedData)
    (some (parameters.outerSecondStartCfg
      { basedData with
        remaining := List.replicate count () ++ basedData.remaining
        innerProcessed := []
        outputReverse :=
          ((repeatTokens parameters.innerCloser count ++
              parameters.frameCloser).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              basedData.outputReverse }))
    (by simpa [basedData] using based) restored
  convert whole using 1
  · simp [basedData, List.map_append, List.reverse_append,
      List.append_assoc]

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
