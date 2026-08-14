/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterConfigurations

/-!
# Input scan of the triangular template emitter

The fixed machine parameters are bundled once for the split execution proof.
The scan retains every workspace symbol, counts both selected classes into
their unary stacks, and reaches the first outer iteration after exactly one
step per input symbol plus the terminal empty-pop step.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

/-- All fixed data of one triangular emitter instance. -/
structure Parameters (Data : Type) where
  firstSelected : Data → Bool
  secondSelected : Data → Bool
  outerFirst : List Recipe
  inner : List Recipe
  outerSecond : List Recipe
  innerBase : List Token
  innerCloser : List Token
  frameCloser : List Token
  finalBase : List Token
  finalCloser : List Token

namespace Parameters

def transition {Data : Type} [Inhabited Data] (parameters : Parameters Data) :=
  TM2.step
    (program parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser)

def scanCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.scanCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

def beginOuterCfg {Data : Type} (parameters : Parameters Data)
    (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.beginOuterCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) data

end Parameters

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

@[simp]
theorem selectedCount_cons {Data : Type} (selected : Data → Bool)
    (workspace : Workspace Data) (workspaces : List (Workspace Data)) :
    selectedCount selected (workspace :: workspaces) =
      (if dataSelected selected workspace then 1 else 0) +
        selectedCount selected workspaces :=
  rfl

theorem replicate_unit_add_one_right (count : Nat) :
    List.replicate (count + 1) () =
      List.replicate count () ++ [()] := by
  rw [List.replicate_add]
  rfl

theorem step_scan_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (inputEq : data.input = []) :
    parameters.transition (parameters.scanCfg data) =
      some (parameters.beginOuterCfg { data with input := [] }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [Parameters.transition, Parameters.scanCfg,
    Parameters.beginOuterCfg, TM2.step, program,
    TriangularTemplateEmitterMachine.scanCfg,
    TriangularTemplateEmitterMachine.beginOuterCfg, cfg, tapes]

theorem step_scan_both {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected parameters.firstSelected workspace = true)
    (secondEq : dataSelected parameters.secondSelected workspace = true) :
    parameters.transition (parameters.scanCfg data) =
      some (parameters.scanCfg
        { data with
          input := tail
          first := () :: data.first
          remaining := () :: data.remaining
          outputReverse := workspace :: data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [Parameters.transition, Parameters.scanCfg, TM2.step, program,
      TriangularTemplateEmitterMachine.scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at firstEq

theorem step_scan_first {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected parameters.firstSelected workspace = true)
    (secondEq : dataSelected parameters.secondSelected workspace = false) :
    parameters.transition (parameters.scanCfg data) =
      some (parameters.scanCfg
        { data with
          input := tail
          first := () :: data.first
          outputReverse := workspace :: data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [Parameters.transition, Parameters.scanCfg, TM2.step, program,
      TriangularTemplateEmitterMachine.scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at firstEq

theorem step_scan_second {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected parameters.firstSelected workspace = false)
    (secondEq : dataSelected parameters.secondSelected workspace = true) :
    parameters.transition (parameters.scanCfg data) =
      some (parameters.scanCfg
        { data with
          input := tail
          remaining := () :: data.remaining
          outputReverse := workspace :: data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [Parameters.transition, Parameters.scanCfg, TM2.step, program,
      TriangularTemplateEmitterMachine.scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at secondEq

theorem step_scan_neither {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (data : TapeData Data)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected parameters.firstSelected workspace = false)
    (secondEq : dataSelected parameters.secondSelected workspace = false) :
    parameters.transition (parameters.scanCfg data) =
      some (parameters.scanCfg
        { data with
          input := tail
          outputReverse := workspace :: data.outputReverse }) := by
  rcases parameters with
    ⟨firstSelected, secondSelected, outerFirst, inner, outerSecond,
      innerBase, innerCloser, frameCloser, finalBase, finalCloser⟩
  rcases data with
    ⟨input, first, remaining, current, processed, innerProcessed,
      firstScratch, positionScratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [Parameters.transition, Parameters.scanCfg, TM2.step, program,
      TriangularTemplateEmitterMachine.scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [Parameters.transition, Parameters.scanCfg, TM2.step, program,
      TriangularTemplateEmitterMachine.scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]

/-- The complete scan retains the word in reverse-output order and materializes
both exact unary selector counts. -/
def scan_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (workspaces : List (Workspace Data))
    (data : TapeData Data) (inputEq : data.input = workspaces) :
    EvalsToInTime parameters.transition
      (parameters.scanCfg data)
      (some (parameters.beginOuterCfg
        { data with
          input := []
          first := List.replicate
              (selectedCount parameters.firstSelected workspaces) () ++
            data.first
          remaining := List.replicate
              (selectedCount parameters.secondSelected workspaces) () ++
            data.remaining
          outputReverse := workspaces.reverse ++ data.outputReverse }))
      (workspaces.length + 1) := by
  induction workspaces generalizing data with
  | nil =>
      have step := oneStep (step_scan_nil parameters data inputEq)
      convert step using 1 <;>
        simp [selectedCount,
          UnaryPolynomialPaddingMachine.selectedCount]
  | cons workspace workspaces induction =>
      by_cases firstEq :
          dataSelected parameters.firstSelected workspace = true
      · by_cases secondEq :
            dataSelected parameters.secondSelected workspace = true
        · let nextData : TapeData Data :=
            { data with
              input := workspaces
              first := () :: data.first
              remaining := () :: data.remaining
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_both parameters data workspace workspaces inputEq
              firstEq secondEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans parameters.transition
            1 (workspaces.length + 1)
            (parameters.scanCfg data) (parameters.scanCfg nextData)
            (some (parameters.beginOuterCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount parameters.firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount parameters.secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstEq, secondEq, if_true]
            rw [show 1 + selectedCount parameters.firstSelected workspaces =
                  selectedCount parameters.firstSelected workspaces + 1 by
                    omega,
              show 1 + selectedCount parameters.secondSelected workspaces =
                  selectedCount parameters.secondSelected workspaces + 1 by
                    omega,
              replicate_unit_add_one_right,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
        · have secondFalse :
              dataSelected parameters.secondSelected workspace = false :=
            Bool.eq_false_of_not_eq_true secondEq
          let nextData : TapeData Data :=
            { data with
              input := workspaces
              first := () :: data.first
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_first parameters data workspace workspaces inputEq
              firstEq secondFalse)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans parameters.transition
            1 (workspaces.length + 1)
            (parameters.scanCfg data) (parameters.scanCfg nextData)
            (some (parameters.beginOuterCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount parameters.firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount parameters.secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstEq, if_true, secondFalse]
            rw [show 1 + selectedCount parameters.firstSelected workspaces =
                  selectedCount parameters.firstSelected workspaces + 1 by
                    omega,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
      · have firstFalse :
            dataSelected parameters.firstSelected workspace = false :=
          Bool.eq_false_of_not_eq_true firstEq
        by_cases secondEq :
            dataSelected parameters.secondSelected workspace = true
        · let nextData : TapeData Data :=
            { data with
              input := workspaces
              remaining := () :: data.remaining
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_second parameters data workspace workspaces inputEq
              firstFalse secondEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans parameters.transition
            1 (workspaces.length + 1)
            (parameters.scanCfg data) (parameters.scanCfg nextData)
            (some (parameters.beginOuterCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount parameters.firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount parameters.secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstFalse, secondEq, if_true]
            rw [show 1 + selectedCount parameters.secondSelected workspaces =
                  selectedCount parameters.secondSelected workspaces + 1 by
                    omega,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
        · have secondFalse :
              dataSelected parameters.secondSelected workspace = false :=
            Bool.eq_false_of_not_eq_true secondEq
          let nextData : TapeData Data :=
            { data with
              input := workspaces
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_neither parameters data workspace workspaces inputEq
              firstFalse secondFalse)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans parameters.transition
            1 (workspaces.length + 1)
            (parameters.scanCfg data) (parameters.scanCfg nextData)
            (some (parameters.beginOuterCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount parameters.firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount parameters.secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp [nextData, selectedCount_cons, firstFalse, secondFalse,
              List.reverse_cons, List.append_assoc]
          · simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
