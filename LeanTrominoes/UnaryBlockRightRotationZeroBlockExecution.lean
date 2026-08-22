/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationCleanupExecution
import LeanTrominoes.UnaryBlockRightRotationFieldSteps

/-! # Executing an empty unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def zeroBlockTime (blockStart : Nat) : Nat :=
  blockCleanupTime blockStart 0 + 1

def zeroBlock_evalsInTime (blockStart : Nat) (data : TapeData)
    (groupEq : data.group = [])
    (startEq : data.start = List.replicate blockStart ())
    (positionEq : data.position = []) :
    EvalsToInTime machine.step (beginGroupCfg data)
      (some (scanSizeFieldCfg
        { data with
          group := []
          start := []
          position := [] }))
      (zeroBlockTime blockStart) := by
  let afterBegin : TapeData := { data with group := [] }
  have beginRun := oneStep (step_beginGroup_nil data groupEq)
  have beginRun' : EvalsToInTime machine.step (beginGroupCfg data)
      (some (clearStartCfg afterBegin)) 1 := by
    simpa [afterBegin] using beginRun
  have cleanupRun := blockCleanup_evalsInTime
    blockStart 0 afterBegin
      (by simpa [afterBegin] using startEq)
      (by simpa [afterBegin] using positionEq)
  have whole := EvalsToInTime.trans machine.step
    1 (blockCleanupTime blockStart 0)
    _ _ _ beginRun' cleanupRun
  simpa only [zeroBlockTime] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
