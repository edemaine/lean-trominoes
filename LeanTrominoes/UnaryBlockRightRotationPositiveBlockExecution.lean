/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationCleanupExecution
import LeanTrominoes.UnaryBlockRightRotationFirstOutputExecution
import LeanTrominoes.UnaryBlockRightRotationRemainingLoopExecution

/-! # Executing one positive unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def positiveBlockOutputReverse (blockStart count : Nat) :
    List UnarySymbol :=
  remainingOutputReverse blockStart 0 count ++
    reversedUnaryField (blockStart + count)

def positiveBlockTime (blockStart count : Nat) : Nat :=
  blockCleanupTime blockStart count +
    (remainingOutputsTime blockStart 0 count +
      firstOutputTime blockStart count)

def positiveBlock_evalsInTime (blockStart count : Nat)
    (data : TapeData)
    (groupEq : data.group = List.replicate (count + 1) ())
    (remainingEq : data.groupRemaining = [])
    (startEq : data.start = List.replicate blockStart ())
    (startRestoreEq : data.startRestore = [])
    (positionEq : data.position = [])
    (positionRestoreEq : data.positionRestore = []) :
    EvalsToInTime machine.step (beginGroupCfg data)
      (some (scanSizeFieldCfg
        { data with
          group := []
          groupRemaining := []
          start := []
          startRestore := []
          position := []
          positionRestore := []
          outputReverse :=
            positiveBlockOutputReverse blockStart count ++
              data.outputReverse }))
      (positiveBlockTime blockStart count) := by
  let afterFirst : TapeData :=
    { data with
      group := []
      groupRemaining := List.replicate count ()
      start := List.replicate blockStart ()
      startRestore := []
      outputReverse :=
        reversedUnaryField (blockStart + count) ++ data.outputReverse }
  have firstRun := firstOutput_evalsInTime blockStart count data
    groupEq remainingEq startEq startRestoreEq
  have firstRun' : EvalsToInTime machine.step (beginGroupCfg data)
      (some (beginRemainingCfg afterFirst))
      (firstOutputTime blockStart count) := by
    simpa [afterFirst, reversedUnaryField] using firstRun
  let afterRemaining : TapeData :=
    { afterFirst with
      groupRemaining := []
      start := List.replicate blockStart ()
      startRestore := []
      position := List.replicate count ()
      positionRestore := []
      outputReverse :=
        remainingOutputReverse blockStart 0 count ++
          (reversedUnaryField (blockStart + count) ++
            data.outputReverse) }
  have remainingRun := remainingOutputs_evalsInTime
    blockStart 0 count afterFirst rfl rfl rfl
      (by simpa [afterFirst] using positionEq)
      (by simpa [afterFirst] using positionRestoreEq)
  have remainingRun' : EvalsToInTime machine.step
      (beginRemainingCfg afterFirst)
      (some (clearStartCfg afterRemaining))
      (remainingOutputsTime blockStart 0 count) := by
    simpa [afterRemaining, afterFirst] using remainingRun
  let afterCleanup : TapeData :=
    { afterRemaining with
      start := []
      position := [] }
  have cleanupRun := blockCleanup_evalsInTime
    blockStart count afterRemaining rfl rfl
  have cleanupRun' : EvalsToInTime machine.step
      (clearStartCfg afterRemaining)
      (some (scanSizeFieldCfg afterCleanup))
      (blockCleanupTime blockStart count) := by
    simpa [afterCleanup] using cleanupRun
  have throughRemaining := EvalsToInTime.trans machine.step
    (firstOutputTime blockStart count)
    (remainingOutputsTime blockStart 0 count)
    _ _ _ firstRun' remainingRun'
  have whole := EvalsToInTime.trans machine.step
    (remainingOutputsTime blockStart 0 count +
      firstOutputTime blockStart count)
    (blockCleanupTime blockStart count)
    _ _ _ throughRemaining cleanupRun'
  convert whole using 1
  · simp only [afterCleanup, afterRemaining, afterFirst,
      positiveBlockOutputReverse, List.append_assoc]
  · simp only [positiveBlockTime]

end LeanTrominoes.UnaryBlockRightRotationMachine

end
