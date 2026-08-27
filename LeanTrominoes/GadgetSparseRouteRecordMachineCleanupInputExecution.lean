/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCleanupSteps
import LeanTrominoes.FiniteBlockTransducer

/-! # Input and horizontal cleanup executions for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

/-- Drain the remaining input tape. -/
def clearInput_evalsInTime (state : State)
    (word : List InputToken) (data : TapeData)
    (inputEq : data.input = word) :
    EvalsToInTime (TM2.step program)
      (clearInputCfg state data)
      (some (clearHorizontalCfg { data with input := [] }))
      (word.length + 1) := by
  induction word generalizing state data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearInput_nil state data inputEq)
      simpa using step
  | cons token word induction =>
      let nextData : TapeData := { data with input := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearInput_cons state data token word inputEq)
      have rest := induction none nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearInputCfg state data)
        (clearInputCfg none nextData)
        (some (clearHorizontalCfg { nextData with input := [] }))
        first rest
      simpa [nextData] using composed

/-- Drain the horizontal counter. -/
def clearHorizontal_evalsInTime (word : List Unit) (data : TapeData)
    (horizontalEq : data.horizontal = word) :
    EvalsToInTime (TM2.step program)
      (clearHorizontalCfg data)
      (some (clearHorizontalComplementCfg
        { data with horizontal := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearHorizontal_nil data horizontalEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with horizontal := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearHorizontal_cons data word horizontalEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearHorizontalCfg data)
        (clearHorizontalCfg nextData)
        (some (clearHorizontalComplementCfg
          { nextData with horizontal := [] })) first rest
      simpa [nextData] using composed

/-- Drain the horizontal complement counter. -/
def clearHorizontalComplement_evalsInTime
    (word : List Unit) (data : TapeData)
    (complementEq : data.horizontalComplement = word) :
    EvalsToInTime (TM2.step program)
      (clearHorizontalComplementCfg data)
      (some (clearVerticalPositiveCfg
        { data with horizontalComplement := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearHorizontalComplement_nil data complementEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData :=
        { data with horizontalComplement := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearHorizontalComplement_cons data word complementEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearHorizontalComplementCfg data)
        (clearHorizontalComplementCfg nextData)
        (some (clearVerticalPositiveCfg
          { nextData with horizontalComplement := [] })) first rest
      simpa [nextData] using composed

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
