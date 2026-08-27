/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCleanupSteps
import LeanTrominoes.FiniteBlockTransducer

/-! # Vertical-counter and scratch cleanup for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

/-- Drain the positive vertical counter. -/
def clearVerticalPositive_evalsInTime
    (word : List Unit) (data : TapeData)
    (positiveEq : data.verticalPositive = word) :
    EvalsToInTime (TM2.step program)
      (clearVerticalPositiveCfg data)
      (some (clearVerticalNegativeCfg
        { data with verticalPositive := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearVerticalPositive_nil data positiveEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with verticalPositive := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearVerticalPositive_cons data word positiveEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearVerticalPositiveCfg data)
        (clearVerticalPositiveCfg nextData)
        (some (clearVerticalNegativeCfg
          { nextData with verticalPositive := [] })) first rest
      simpa [nextData] using composed

/-- Drain the negative vertical counter. -/
def clearVerticalNegative_evalsInTime
    (word : List Unit) (data : TapeData)
    (negativeEq : data.verticalNegative = word) :
    EvalsToInTime (TM2.step program)
      (clearVerticalNegativeCfg data)
      (some (clearScratchCfg { data with verticalNegative := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearVerticalNegative_nil data negativeEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with verticalNegative := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearVerticalNegative_cons data word negativeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearVerticalNegativeCfg data)
        (clearVerticalNegativeCfg nextData)
        (some (clearScratchCfg
          { nextData with verticalNegative := [] })) first rest
      simpa [nextData] using composed

/-- Drain the scratch tape and halt. -/
def clearScratch_evalsInTime (word : List Unit) (data : TapeData)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step program)
      (clearScratchCfg data)
      (some (haltCfg { data with scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearScratch_nil data scratchEq)
      simpa using step
  | cons head word induction =>
      rcases head with ⟨⟩
      let nextData : TapeData := { data with scratch := word }
      have first := FiniteBlockTransducer.oneStep
        (step_clearScratch_cons data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (clearScratchCfg data)
        (clearScratchCfg nextData)
        (some (haltCfg { nextData with scratch := [] })) first rest
      simpa [nextData] using composed

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
