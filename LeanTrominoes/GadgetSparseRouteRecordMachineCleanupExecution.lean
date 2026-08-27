/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCleanupInputExecution
import LeanTrominoes.GadgetSparseRouteRecordMachineCleanupCounterExecution

/-! # Complete terminal cleanup for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

/-- Tape contents after terminal cleanup. -/
def clearedData (data : TapeData) : TapeData :=
  { data with
    input := []
    horizontal := []
    horizontalComplement := []
    verticalPositive := []
    verticalNegative := []
    scratch := [] }

/-- Exact running time of terminal cleanup. -/
def cleanupTime (data : TapeData) : Nat :=
  data.input.length + data.horizontal.length +
    data.horizontalComplement.length + data.verticalPositive.length +
    data.verticalNegative.length + data.scratch.length + 6

/-- Drain every non-output tape and halt. -/
def cleanup_evalsInTime (state : State) (data : TapeData) :
    EvalsToInTime (TM2.step program)
      (clearInputCfg state data)
      (some (haltCfg (clearedData data)))
      (cleanupTime data) := by
  let d1 : TapeData := { data with input := [] }
  let d2 : TapeData := { d1 with horizontal := [] }
  let d3 : TapeData := { d2 with horizontalComplement := [] }
  let d4 : TapeData := { d3 with verticalPositive := [] }
  let d5 : TapeData := { d4 with verticalNegative := [] }
  let d6 : TapeData := { d5 with scratch := [] }

  have inputRun : EvalsToInTime (TM2.step program)
      (clearInputCfg state data) (some (clearHorizontalCfg d1))
      (data.input.length + 1) := by
    simpa [d1] using clearInput_evalsInTime state data.input data rfl
  have horizontalRun : EvalsToInTime (TM2.step program)
      (clearHorizontalCfg d1) (some (clearHorizontalComplementCfg d2))
      (data.horizontal.length + 1) := by
    simpa [d1, d2] using
      clearHorizontal_evalsInTime data.horizontal d1 (by simp [d1])
  have complementRun : EvalsToInTime (TM2.step program)
      (clearHorizontalComplementCfg d2)
      (some (clearVerticalPositiveCfg d3))
      (data.horizontalComplement.length + 1) := by
    simpa [d1, d2, d3] using
      clearHorizontalComplement_evalsInTime
        data.horizontalComplement d2 (by simp [d1, d2])
  have positiveRun : EvalsToInTime (TM2.step program)
      (clearVerticalPositiveCfg d3)
      (some (clearVerticalNegativeCfg d4))
      (data.verticalPositive.length + 1) := by
    simpa [d1, d2, d3, d4] using
      clearVerticalPositive_evalsInTime
        data.verticalPositive d3 (by simp [d1, d2, d3])
  have negativeRun : EvalsToInTime (TM2.step program)
      (clearVerticalNegativeCfg d4) (some (clearScratchCfg d5))
      (data.verticalNegative.length + 1) := by
    simpa [d1, d2, d3, d4, d5] using
      clearVerticalNegative_evalsInTime
        data.verticalNegative d4 (by simp [d1, d2, d3, d4])
  have scratchRun : EvalsToInTime (TM2.step program)
      (clearScratchCfg d5) (some (haltCfg d6))
      (data.scratch.length + 1) := by
    simpa [d1, d2, d3, d4, d5, d6] using
      clearScratch_evalsInTime data.scratch d5
        (by simp [d1, d2, d3, d4, d5])

  have throughHorizontal := EvalsToInTime.trans (TM2.step program)
    (data.input.length + 1) (data.horizontal.length + 1)
    (clearInputCfg state data) (clearHorizontalCfg d1)
    (some (clearHorizontalComplementCfg d2)) inputRun horizontalRun
  have throughComplement := EvalsToInTime.trans (TM2.step program)
    (data.horizontal.length + 1 + (data.input.length + 1))
    (data.horizontalComplement.length + 1)
    (clearInputCfg state data) (clearHorizontalComplementCfg d2)
    (some (clearVerticalPositiveCfg d3)) throughHorizontal complementRun
  have throughPositive := EvalsToInTime.trans (TM2.step program)
    (data.horizontalComplement.length + 1 +
      (data.horizontal.length + 1 + (data.input.length + 1)))
    (data.verticalPositive.length + 1)
    (clearInputCfg state data) (clearVerticalPositiveCfg d3)
    (some (clearVerticalNegativeCfg d4)) throughComplement positiveRun
  have throughNegative := EvalsToInTime.trans (TM2.step program)
    (data.verticalPositive.length + 1 +
      (data.horizontalComplement.length + 1 +
        (data.horizontal.length + 1 + (data.input.length + 1))))
    (data.verticalNegative.length + 1)
    (clearInputCfg state data) (clearVerticalNegativeCfg d4)
    (some (clearScratchCfg d5)) throughPositive negativeRun
  have whole := EvalsToInTime.trans (TM2.step program)
    (data.verticalNegative.length + 1 +
      (data.verticalPositive.length + 1 +
        (data.horizontalComplement.length + 1 +
          (data.horizontal.length + 1 + (data.input.length + 1)))))
    (data.scratch.length + 1)
    (clearInputCfg state data) (clearScratchCfg d5)
    (some (haltCfg d6)) throughNegative scratchRun
  convert whole using 1
  · simp [clearedData, d1, d2, d3, d4, d5, d6]
  · simp [cleanupTime]
    omega

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
