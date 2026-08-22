/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationFirstGroupExecution
import LeanTrominoes.UnaryBlockRightRotationFirstStartExecution
import LeanTrominoes.UnaryBlockRightRotationFieldSteps

/-! # Emitting the first value of a right-rotated unary block -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def firstOutputTime (blockStart count : Nat) : Nat :=
  2 * blockStart + count + 5

def firstOutput_evalsInTime (blockStart count : Nat) (data : TapeData)
    (groupEq : data.group = List.replicate (count + 1) ())
    (remainingEq : data.groupRemaining = [])
    (startEq : data.start = List.replicate blockStart ())
    (restoreEq : data.startRestore = []) :
    EvalsToInTime machine.step (beginGroupCfg data)
      (some (beginRemainingCfg
        { data with
          group := []
          groupRemaining := List.replicate count ()
          start := List.replicate blockStart ()
          startRestore := []
          outputReverse := .delimiter ::
            (List.replicate (blockStart + count) .unit ++
              data.outputReverse) }))
      (firstOutputTime blockStart count) := by
  let afterBegin : TapeData :=
    { data with group := List.replicate count () }
  have groupHead : data.group = () :: List.replicate count () := by
    simpa [List.replicate_succ] using groupEq
  have beginRun := oneStep
    (step_beginGroup_cons data (List.replicate count ()) groupHead)
  have beginRun' : EvalsToInTime machine.step (beginGroupCfg data)
      (some (copyFirstStartCfg afterBegin)) 1 := by
    simpa [afterBegin] using beginRun
  let afterCopyStart : TapeData :=
    { afterBegin with
      start := []
      startRestore := List.replicate blockStart ()
      outputReverse :=
        List.replicate blockStart .unit ++ data.outputReverse }
  have copyStartRun := copyFirstStart_evalsInTime
    blockStart afterBegin (by simpa [afterBegin] using startEq)
  have copyStartRun' : EvalsToInTime machine.step
      (copyFirstStartCfg afterBegin)
      (some (restoreFirstStartCfg afterCopyStart))
      (blockStart + 1) := by
    simpa [afterBegin, afterCopyStart, restoreEq]
      using copyStartRun
  let afterRestoreStart : TapeData :=
    { afterCopyStart with
      startRestore := []
      start := List.replicate blockStart () }
  have restoreStartRun := restoreFirstStart_evalsInTime
    blockStart afterCopyStart rfl
  have restoreStartRun' : EvalsToInTime machine.step
      (restoreFirstStartCfg afterCopyStart)
      (some (copyFirstGroupCfg afterRestoreStart))
      (blockStart + 1) := by
    simpa [afterCopyStart, afterRestoreStart, afterBegin, startEq]
      using restoreStartRun
  let afterCopyGroup : TapeData :=
    { afterRestoreStart with
      group := []
      groupRemaining := List.replicate count ()
      outputReverse :=
        List.replicate count .unit ++
          (List.replicate blockStart .unit ++ data.outputReverse) }
  have copyGroupRun := copyFirstGroup_evalsInTime
    count afterRestoreStart rfl
  have copyGroupRun' : EvalsToInTime machine.step
      (copyFirstGroupCfg afterRestoreStart)
      (some (emitFirstDelimiterCfg afterCopyGroup))
      (count + 1) := by
    simpa only [afterRestoreStart, afterCopyStart, afterBegin,
      afterCopyGroup, remainingEq, restoreEq, startEq,
      List.append_nil] using copyGroupRun
  let afterDelimiter : TapeData :=
    { afterCopyGroup with
      outputReverse := .delimiter :: afterCopyGroup.outputReverse }
  have delimiterRun := oneStep (step_emitFirstDelimiter afterCopyGroup)
  have delimiterRun' : EvalsToInTime machine.step
      (emitFirstDelimiterCfg afterCopyGroup)
      (some (beginRemainingCfg afterDelimiter)) 1 := by
    simpa [afterDelimiter] using delimiterRun
  have throughCopyStart := EvalsToInTime.trans machine.step
    1 (blockStart + 1) _ _ _ beginRun' copyStartRun'
  have throughRestoreStart := EvalsToInTime.trans machine.step
    (blockStart + 1 + 1) (blockStart + 1)
    _ _ _ throughCopyStart restoreStartRun'
  have throughCopyGroup := EvalsToInTime.trans machine.step
    (blockStart + 1 + (blockStart + 1 + 1)) (count + 1)
    _ _ _ throughRestoreStart copyGroupRun'
  have whole := EvalsToInTime.trans machine.step
    (count + 1 + (blockStart + 1 + (blockStart + 1 + 1))) 1
    _ _ _ throughCopyGroup delimiterRun'
  have outputEq :
      .delimiter ::
          (List.replicate count .unit ++
            (List.replicate blockStart .unit ++ data.outputReverse)) =
        .delimiter ::
          (List.replicate (blockStart + count) .unit ++
            data.outputReverse) := by
    rw [← List.append_assoc, ← List.replicate_add,
      Nat.add_comm count blockStart]
  convert whole using 1
  · simp only [afterDelimiter, afterCopyGroup, afterRestoreStart,
      afterCopyStart, afterBegin, outputEq]
  · simp only [firstOutputTime]
    omega

end LeanTrominoes.UnaryBlockRightRotationMachine

end
