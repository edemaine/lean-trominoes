/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachinePixelExecution

/-! # Cleanup and reversal executions for sparse assignment tokens -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

/-- Drain the horizontal work tape. -/
def clearHorizontal_evalsInTime (tromino : Tromino)
    (target : ResetTarget) (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word) :
    EvalsToInTime (TM2.step (program tromino))
      (clearHorizontalCfg target data)
      (some (clearVerticalCfg target { data with horizontal := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearHorizontal_nil tromino data target horizontalEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with horizontal := word }
      have first := oneStep
        (step_clearHorizontal_cons tromino data target word horizontalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (clearHorizontalCfg target data)
        (clearHorizontalCfg target nextData)
        (some (clearVerticalCfg target
          { nextData with horizontal := [] })) first rest
      simpa using composed

/-- Drain the vertical work tape and enter the selected continuation. -/
def clearVertical_evalsInTime (tromino : Tromino)
    (target : ResetTarget) (word : List Unit) (data : TapeData)
    (verticalEq : data.vertical = word) :
    EvalsToInTime (TM2.step (program tromino))
      (clearVerticalCfg target data)
      (some (cfg (afterClear target) none { data with vertical := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearVertical_nil tromino data target verticalEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with vertical := word }
      have first := oneStep
        (step_clearVertical_cons tromino data target word verticalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (clearVerticalCfg target data)
        (clearVerticalCfg target nextData)
        (some (cfg (afterClear target) none
          { nextData with vertical := [] })) first rest
      simpa using composed

/-- Drain both coordinate work tapes. -/
def clear_evalsInTime (tromino : Tromino)
    (target : ResetTarget) (horizontal vertical : List Unit)
    (data : TapeData) (horizontalEq : data.horizontal = horizontal)
    (verticalEq : data.vertical = vertical) :
    EvalsToInTime (TM2.step (program tromino))
      (clearHorizontalCfg target data)
      (some (cfg (afterClear target) none
        { data with horizontal := [], vertical := [] }))
      (horizontal.length + vertical.length + 2) := by
  have first := clearHorizontal_evalsInTime tromino target horizontal data
    horizontalEq
  let horizontalCleared : TapeData := { data with horizontal := [] }
  have second := clearVertical_evalsInTime tromino target vertical
    horizontalCleared (by simpa [horizontalCleared] using verticalEq)
  have composed := EvalsToInTime.trans (TM2.step (program tromino))
    (horizontal.length + 1) (vertical.length + 1)
    (clearHorizontalCfg target data)
    (clearVerticalCfg target horizontalCleared)
    (some (cfg (afterClear target) none
      { horizontalCleared with vertical := [] })) first
    (by simpa [horizontalCleared] using second)
  convert composed using 1
  omega

/-- Reverse the accumulated prepared output onto the designated output tape. -/
def reverseOutput_evalsInTime (tromino : Tromino)
    (word : List OutputToken) (data : TapeData)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step (program tromino))
      (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil tromino data outputReverseEq)
      convert step using 1 <;> simp
  | cons token word induction =>
      let nextData : TapeData :=
        { data with
          outputReverse := word
          output := token :: data.output }
      have first := oneStep
        (step_reverseOutput_cons tromino data token word outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program tromino))
        1 (word.length + 1)
        (reverseOutputCfg data) (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
