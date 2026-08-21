/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterConfigurations

/-! # Input scan for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

@[simp] theorem selectedCount_cons {Data : Type} (selected : Data → Bool)
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

@[simp] theorem replicate_unit_one_add (count : Nat) :
    List.replicate (1 + count) () =
      List.replicate count () ++ [()] := by
  rw [Nat.add_comm, replicate_unit_add_one_right]

def afterScanItem {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (workspace : Workspace Data) (tail : List (Workspace Data))
    (data : TapeData Data) : TapeData Data :=
  { data with
    input := tail
    first := if dataSelected firstSelected workspace then
        () :: data.first else data.first
    second := if dataSelected secondSelected workspace then
        () :: data.second else data.second
    remaining := if dataSelected positionSelected workspace then
        () :: data.remaining else data.remaining
    outputReverse := workspace :: data.outputReverse }

theorem step_scan_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (inputEq : data.input = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanCfg data) =
      some (beginPositionCfg { data with input := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, beginPositionCfg, cfg, tapes]

theorem step_scan_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanCfg data) =
      some (scanCfg
        (afterScanItem firstSelected secondSelected positionSelected
          workspace tail data)) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · cases firstEq : firstSelected dataValue <;>
      cases secondEq : secondSelected dataValue <;>
      cases positionEq : positionSelected dataValue <;>
      simp [TM2.step, program, scanCfg, cfg, tapes, afterScanItem,
        countAll, countSecondAndPosition, countPosition, continueScan,
        workspaceFromState, stateSelected, dataSelected,
        firstEq, secondEq, positionEq]
  · simp [TM2.step, program, scanCfg, cfg, tapes, afterScanItem,
      countAll, countSecondAndPosition, countPosition, continueScan,
      workspaceFromState, stateSelected, dataSelected]

/-- Scanning retains the input in reverse, materializes all three selected
counts as unary stacks, and takes one step per symbol plus the terminal pop. -/
def scan_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspaces : List (Workspace Data)) (data : TapeData Data)
    (inputEq : data.input = workspaces) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (scanCfg data)
      (some (beginPositionCfg
        { data with
          input := []
          first :=
            List.replicate (selectedCount firstSelected workspaces) () ++
              data.first
          second :=
            List.replicate (selectedCount secondSelected workspaces) () ++
              data.second
          remaining :=
            List.replicate (selectedCount positionSelected workspaces) () ++
              data.remaining
          outputReverse := workspaces.reverse ++ data.outputReverse }))
      (workspaces.length + 1) := by
  induction workspaces generalizing data with
  | nil =>
      have step := oneStep
        (step_scan_nil firstSelected secondSelected positionSelected
          recipes ending data inputEq)
      convert step using 1 <;>
        simp [selectedCount,
          UnaryPolynomialPaddingMachine.selectedCount]
  | cons workspace workspaces induction =>
      let nextData := afterScanItem firstSelected secondSelected
        positionSelected workspace workspaces data
      have firstStep := oneStep
        (step_scan_cons firstSelected secondSelected positionSelected
          recipes ending data workspace workspaces inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
        (some (beginPositionCfg
          { nextData with
            input := []
            first := List.replicate
                (selectedCount firstSelected workspaces) () ++
              nextData.first
            second := List.replicate
                (selectedCount secondSelected workspaces) () ++
              nextData.second
            remaining := List.replicate
                (selectedCount positionSelected workspaces) () ++
              nextData.remaining
            outputReverse :=
              workspaces.reverse ++ nextData.outputReverse }))
        firstStep rest
      cases firstEq : dataSelected firstSelected workspace <;>
        cases secondEq : dataSelected secondSelected workspace <;>
        cases positionEq : dataSelected positionSelected workspace <;>
        convert composed using 1 <;>
        simp [nextData, afterScanItem, selectedCount_cons,
          firstEq, secondEq, positionEq, replicate_unit_one_add,
          List.reverse_cons, List.append_assoc, Nat.add_comm]

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
