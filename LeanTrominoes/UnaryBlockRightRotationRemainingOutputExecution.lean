/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationPositionExecution
import LeanTrominoes.UnaryBlockRightRotationRemainingStartExecution

/-! # Emitting one remaining value of a right-rotated unary block -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def remainingOutputTime (blockStart position : Nat) : Nat :=
  2 * blockStart + 2 * position + 6

def remainingOutput_evalsInTime (blockStart position : Nat)
    (remaining : List Unit) (data : TapeData)
    (remainingEq : data.groupRemaining = () :: remaining)
    (startEq : data.start = List.replicate blockStart ())
    (startRestoreEq : data.startRestore = [])
    (positionEq : data.position = List.replicate position ())
    (positionRestoreEq : data.positionRestore = []) :
    EvalsToInTime machine.step (beginRemainingCfg data)
      (some (beginRemainingCfg
        { data with
          groupRemaining := remaining
          start := List.replicate blockStart ()
          startRestore := []
          position := List.replicate (position + 1) ()
          positionRestore := []
          outputReverse := .delimiter ::
            (List.replicate (blockStart + position) .unit ++
              data.outputReverse) }))
      (remainingOutputTime blockStart position) := by
  let afterBegin : TapeData :=
    { data with groupRemaining := remaining }
  have beginRun := oneStep
    (step_beginRemaining_cons data remaining remainingEq)
  have beginRun' : EvalsToInTime machine.step (beginRemainingCfg data)
      (some (copyRemainingStartCfg afterBegin)) 1 := by
    simpa [afterBegin] using beginRun
  let afterCopyStart : TapeData :=
    { afterBegin with
      start := []
      startRestore := List.replicate blockStart ()
      outputReverse :=
        List.replicate blockStart .unit ++ data.outputReverse }
  have copyStartRun := copyRemainingStart_evalsInTime
    blockStart afterBegin (by simpa [afterBegin] using startEq)
  have copyStartRun' : EvalsToInTime machine.step
      (copyRemainingStartCfg afterBegin)
      (some (restoreRemainingStartCfg afterCopyStart))
      (blockStart + 1) := by
    simpa [afterBegin, afterCopyStart, startRestoreEq]
      using copyStartRun
  let afterRestoreStart : TapeData :=
    { afterCopyStart with
      startRestore := []
      start := List.replicate blockStart () }
  have restoreStartRun := restoreRemainingStart_evalsInTime
    blockStart afterCopyStart rfl
  have restoreStartRun' : EvalsToInTime machine.step
      (restoreRemainingStartCfg afterCopyStart)
      (some (copyPositionCfg afterRestoreStart))
      (blockStart + 1) := by
    simpa [afterCopyStart, afterRestoreStart, afterBegin, startEq]
      using restoreStartRun
  let afterCopyPosition : TapeData :=
    { afterRestoreStart with
      position := []
      positionRestore := List.replicate position ()
      outputReverse :=
        List.replicate position .unit ++
          (List.replicate blockStart .unit ++ data.outputReverse) }
  have copyPositionRun := copyPosition_evalsInTime
    position afterRestoreStart
      (by simpa [afterRestoreStart, afterCopyStart, afterBegin]
        using positionEq)
  have copyPositionRun' : EvalsToInTime machine.step
      (copyPositionCfg afterRestoreStart)
      (some (restorePositionCfg afterCopyPosition))
      (position + 1) := by
    simpa only [afterRestoreStart, afterCopyStart, afterBegin,
      afterCopyPosition, positionRestoreEq, List.append_nil]
      using copyPositionRun
  let afterRestorePosition : TapeData :=
    { afterCopyPosition with
      positionRestore := []
      position := List.replicate position () }
  have restorePositionRun := restorePosition_evalsInTime
    position afterCopyPosition rfl
  have restorePositionRun' : EvalsToInTime machine.step
      (restorePositionCfg afterCopyPosition)
      (some (emitRemainingDelimiterCfg afterRestorePosition))
      (position + 1) := by
    simpa [afterCopyPosition, afterRestorePosition,
      afterRestoreStart, afterCopyStart, afterBegin, positionEq]
      using restorePositionRun
  let afterDelimiter : TapeData :=
    { afterRestorePosition with
      position := () :: afterRestorePosition.position
      outputReverse := .delimiter :: afterRestorePosition.outputReverse }
  have delimiterRun := oneStep
    (step_emitRemainingDelimiter afterRestorePosition)
  have delimiterRun' : EvalsToInTime machine.step
      (emitRemainingDelimiterCfg afterRestorePosition)
      (some (beginRemainingCfg afterDelimiter)) 1 := by
    simpa [afterDelimiter] using delimiterRun
  have throughCopyStart := EvalsToInTime.trans machine.step
    1 (blockStart + 1) _ _ _ beginRun' copyStartRun'
  have throughRestoreStart := EvalsToInTime.trans machine.step
    (blockStart + 1 + 1) (blockStart + 1)
    _ _ _ throughCopyStart restoreStartRun'
  have throughCopyPosition := EvalsToInTime.trans machine.step
    (blockStart + 1 + (blockStart + 1 + 1)) (position + 1)
    _ _ _ throughRestoreStart copyPositionRun'
  have throughRestorePosition := EvalsToInTime.trans machine.step
    (position + 1 + (blockStart + 1 + (blockStart + 1 + 1)))
    (position + 1) _ _ _ throughCopyPosition restorePositionRun'
  have whole := EvalsToInTime.trans machine.step
    (position + 1 +
      (position + 1 + (blockStart + 1 + (blockStart + 1 + 1))))
    1 _ _ _ throughRestorePosition delimiterRun'
  have outputEq :
      .delimiter ::
          (List.replicate position .unit ++
            (List.replicate blockStart .unit ++ data.outputReverse)) =
        .delimiter ::
          (List.replicate (blockStart + position) .unit ++
            data.outputReverse) := by
    rw [← List.append_assoc, ← List.replicate_add,
      Nat.add_comm position blockStart]
  convert whole using 1
  · simp only [afterDelimiter, afterRestorePosition,
      afterCopyPosition, afterRestoreStart, afterCopyStart, afterBegin,
      outputEq, List.replicate_succ]
  · simp only [remainingOutputTime]
    omega

end LeanTrominoes.UnaryBlockRightRotationMachine

end
