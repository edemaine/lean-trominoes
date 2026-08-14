/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterFinalFold

/-!
# Counter cleanup and output reversal of the triangular emitter

The persistent first counter is cleared exactly, then the accumulated reverse
workspace is moved to the output stack.  The final theorem is generic in the
workspace word and proves both exact forward output and genuine halting.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

namespace Parameters

def reverseOutputCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.reverseOutputCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

def haltDataCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.haltDataCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

end Parameters

theorem step_clearFirst_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (firstEq : data.first = []) :
    parameters.transition (parameters.clearFirstCfg data) =
      some (parameters.reverseOutputCfg { data with first := [] }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [Parameters.transition, Parameters.clearFirstCfg,
    Parameters.reverseOutputCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.clearFirstCfg,
    TriangularTemplateEmitterMachine.reverseOutputCfg, cfg, tapes]

theorem step_clearFirst_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (tail : List Unit) (firstEq : data.first = () :: tail) :
    parameters.transition (parameters.clearFirstCfg data) =
      some (parameters.clearFirstCfg { data with first := tail }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change first = () :: tail at firstEq
  subst first
  simp [Parameters.transition, Parameters.clearFirstCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.clearFirstCfg, cfg, tapes]

theorem step_reverseOutput_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (outputReverseEq : data.outputReverse = []) :
    parameters.transition (parameters.reverseOutputCfg data) =
      some (parameters.haltDataCfg { data with outputReverse := [] }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [Parameters.transition, Parameters.reverseOutputCfg,
    Parameters.haltDataCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.reverseOutputCfg,
    TriangularTemplateEmitterMachine.haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (outputReverseEq : data.outputReverse = workspace :: tail) :
    parameters.transition (parameters.reverseOutputCfg data) =
      some (parameters.reverseOutputCfg
        { data with
          outputReverse := tail
          output := workspace :: data.output }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change outputReverse = workspace :: tail at outputReverseEq
  subst outputReverse
  rcases workspace with dataValue | token <;>
    simp [Parameters.transition, Parameters.reverseOutputCfg,
      TM2.step, program, TriangularTemplateEmitterMachine.reverseOutputCfg,
      cfg, tapes, workspaceFromState]

/-- Clear the persistent first counter. -/
def clearFirst_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime parameters.transition
      (parameters.clearFirstCfg data)
      (some (parameters.reverseOutputCfg { data with first := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearFirst_nil parameters data firstEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with first := word }
      have firstStep := oneStep
        (step_clearFirst_cons parameters data word firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition 1
        (word.length + 1) (parameters.clearFirstCfg data)
        (parameters.clearFirstCfg nextData)
        (some (parameters.reverseOutputCfg { nextData with first := [] }))
        firstStep rest
      simpa using composed

/-- Reverse the accumulated workspace onto the output stack and halt. -/
def reverseOutput_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (word : List (Workspace Data))
    (data : TapeData Data) (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime parameters.transition
      (parameters.reverseOutputCfg data)
      (some (parameters.haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil parameters data outputReverseEq)
      convert step using 1
      all_goals simp
  | cons workspace word induction =>
      let nextData : TapeData Data :=
        { data with
          outputReverse := word
          output := workspace :: data.output }
      have firstStep := oneStep
        (step_reverseOutput_cons parameters data workspace word
          outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition 1
        (word.length + 1) (parameters.reverseOutputCfg data)
        (parameters.reverseOutputCfg nextData)
        (some (parameters.haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
