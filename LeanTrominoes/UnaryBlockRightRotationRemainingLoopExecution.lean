/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationRemainingOutputExecution

/-! # Emitting all remaining values of a right-rotated unary block -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def reversedUnaryField (value : Nat) : List UnarySymbol :=
  .delimiter :: List.replicate value .unit

def remainingOutputReverse (blockStart position : Nat) :
    Nat → List UnarySymbol
  | 0 => []
  | count + 1 =>
      remainingOutputReverse blockStart (position + 1) count ++
        reversedUnaryField (blockStart + position)

def remainingOutputsTime (blockStart position : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      remainingOutputsTime blockStart (position + 1) count +
        remainingOutputTime blockStart position

def remainingOutputs_evalsInTime (blockStart position count : Nat)
    (data : TapeData)
    (remainingEq : data.groupRemaining = List.replicate count ())
    (startEq : data.start = List.replicate blockStart ())
    (startRestoreEq : data.startRestore = [])
    (positionEq : data.position = List.replicate position ())
    (positionRestoreEq : data.positionRestore = []) :
    EvalsToInTime machine.step (beginRemainingCfg data)
      (some (clearStartCfg
        { data with
          groupRemaining := []
          start := List.replicate blockStart ()
          startRestore := []
          position := List.replicate (position + count) ()
          positionRestore := []
          outputReverse :=
            remainingOutputReverse blockStart position count ++
              data.outputReverse }))
      (remainingOutputsTime blockStart position count) := by
  induction count generalizing position data with
  | zero =>
      have step := step_beginRemaining_nil data
        (by simpa using remainingEq)
      simpa [remainingOutputsTime, remainingOutputReverse,
        startEq, startRestoreEq, positionEq, positionRestoreEq]
        using oneStep step
  | succ count induction =>
      have remainingHead : data.groupRemaining =
          () :: List.replicate count () := by
        simpa [List.replicate_succ] using remainingEq
      let afterFirst : TapeData :=
        { data with
          groupRemaining := List.replicate count ()
          start := List.replicate blockStart ()
          startRestore := []
          position := List.replicate (position + 1) ()
          positionRestore := []
          outputReverse :=
            reversedUnaryField (blockStart + position) ++
              data.outputReverse }
      have firstRun := remainingOutput_evalsInTime
        blockStart position (List.replicate count ()) data
        remainingHead startEq startRestoreEq positionEq positionRestoreEq
      have firstRun' : EvalsToInTime machine.step
          (beginRemainingCfg data)
          (some (beginRemainingCfg afterFirst))
          (remainingOutputTime blockStart position) := by
        simpa [afterFirst, reversedUnaryField] using firstRun
      have restRun := induction (position := position + 1)
        afterFirst rfl rfl rfl rfl rfl
      have whole := EvalsToInTime.trans machine.step
        (remainingOutputTime blockStart position)
        (remainingOutputsTime blockStart (position + 1) count)
        _ _ _ firstRun' restRun
      convert whole using 1
      · simp only [afterFirst, remainingOutputReverse,
          List.append_assoc]
        congr 4
        omega
      · simp only [remainingOutputsTime]

end LeanTrominoes.UnaryBlockRightRotationMachine

end
