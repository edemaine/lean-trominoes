/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterRange

/-!
# Final fold of the triangular emitter

When no outer markers remain, the machine emits the final base and removes
every completed outer marker while emitting one final closer.  The resulting
configuration has an empty `processed` stack and is ready to clear the
persistent first counter.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

namespace Parameters

def unwindCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.unwindCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

def clearFirstCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.clearFirstCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

end Parameters

theorem step_beginOuter_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (remainingEq : data.remaining = []) :
    parameters.transition (parameters.beginOuterCfg data) =
      some (parameters.unwindCfg
        { data with
          remaining := []
          outputReverse :=
            (parameters.finalBase.map fun token =>
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
  simp [Parameters.transition, Parameters.beginOuterCfg,
    Parameters.unwindCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.beginOuterCfg,
    TriangularTemplateEmitterMachine.unwindCfg, cfg, tapes,
    stepAux_pushTokens]

theorem step_unwind_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (tail : List Unit) (processedEq : data.processed = () :: tail) :
    parameters.transition (parameters.unwindCfg data) =
      some (parameters.unwindCfg
        { data with
          processed := tail
          outputReverse :=
            (parameters.finalCloser.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp [Parameters.transition, Parameters.unwindCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.unwindCfg, cfg, tapes,
    stepAux_pushTokens]

theorem step_unwind_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (processedEq : data.processed = []) :
    parameters.transition (parameters.unwindCfg data) =
      some (parameters.clearFirstCfg { data with processed := [] }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [Parameters.transition, Parameters.unwindCfg,
    Parameters.clearFirstCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.unwindCfg,
    TriangularTemplateEmitterMachine.clearFirstCfg, cfg, tapes]

/-- Remove all completed outer markers and emit one final closer per marker. -/
def unwind_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (count : Nat) (data : TapeData Data)
    (processedEq : data.processed = List.replicate count ()) :
    EvalsToInTime parameters.transition
      (parameters.unwindCfg data)
      (some (parameters.clearFirstCfg
        { data with
          processed := []
          outputReverse :=
            ((repeatTokens parameters.finalCloser count).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := oneStep
        (step_unwind_nil parameters data (by simpa using processedEq))
      convert step using 1
      all_goals simp [repeatTokens]
  | succ count induction =>
      let nextData : TapeData Data :=
        { data with
          processed := List.replicate count ()
          outputReverse :=
            (parameters.finalCloser.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }
      have firstStep := oneStep
        (step_unwind_cons parameters data (List.replicate count ()) (by
          simpa [List.replicate_succ] using processedEq))
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition 1
        (count + 1) (parameters.unwindCfg data)
        (parameters.unwindCfg nextData)
        (some (parameters.clearFirstCfg
          { nextData with
            processed := []
            outputReverse :=
              ((repeatTokens parameters.finalCloser count).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  nextData.outputReverse }))
        (by simpa [nextData] using firstStep) rest
      convert composed using 1
      simp [nextData, repeatTokens, List.map_append, List.reverse_append,
        List.append_assoc]

/-- Emit the final base and the complete outer unwind suffix. -/
def finishOuterRange_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (count : Nat) (data : TapeData Data)
    (remainingEq : data.remaining = [])
    (processedEq : data.processed = List.replicate count ()) :
    EvalsToInTime parameters.transition
      (parameters.beginOuterCfg data)
      (some (parameters.clearFirstCfg
        { data with
          remaining := []
          processed := []
          outputReverse :=
            ((parameters.finalBase ++
                repeatTokens parameters.finalCloser count).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (count + 2) := by
  let basedData : TapeData Data :=
    { data with
      remaining := []
      outputReverse :=
        (parameters.finalBase.map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++
            data.outputReverse }
  have based := oneStep (step_beginOuter_nil parameters data remainingEq)
  have unwound := unwind_evalsInTime parameters count basedData (by
    simpa [basedData] using processedEq)
  have whole := EvalsToInTime.trans parameters.transition 1 (count + 1)
    (parameters.beginOuterCfg data) (parameters.unwindCfg basedData)
    (some (parameters.clearFirstCfg
      { basedData with
        processed := []
        outputReverse :=
          ((repeatTokens parameters.finalCloser count).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              basedData.outputReverse }))
    (by simpa [basedData] using based) unwound
  convert whole using 1
  simp [basedData, List.map_append, List.reverse_append,
    List.append_assoc]

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
