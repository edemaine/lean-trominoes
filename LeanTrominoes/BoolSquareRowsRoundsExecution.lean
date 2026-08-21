/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsLastRoundExecution
import LeanTrominoes.BoolSquareRowsNextRoundExecution
import LeanTrominoes.BoolSquareRowsRoundArithmetic

/-! # Complete square-root counter rounds -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

/-- Cost of `additionalRounds` nonfinal rounds followed by one final round. -/
def rootRoundsCost : Nat → Nat → Nat
  | completed, 0 => lastRootRoundCost completed
  | completed, additionalRounds + 1 =>
      nextRootRoundCost completed +
        rootRoundsCost (completed + 1) additionalRounds

/-- Starting with exactly a positive square's remaining work, the machine
completes all odd intervals and enters counter cleanup. -/
def rootRounds_evalsInTime (completed additionalRounds : Nat)
    (data : TapeData)
    (workEq : data.work = List.replicate
      (remainingWork completed (additionalRounds + 1)) ())
    (oddEq : data.odd = List.replicate (2 * completed + 1) ())
    (restoreEq : data.oddRestore = []) :
    EvalsToInTime (TM2.step program) (consumeWorkCfg data)
      (some (clearOddCfg
        { data with
          work := []
          odd := []
          oddRestore :=
            List.replicate (2 * (completed + additionalRounds) + 1) ()
          root := List.replicate (additionalRounds + 1) () ++ data.root }))
      (rootRoundsCost completed additionalRounds) := by
  induction additionalRounds generalizing completed data with
  | zero =>
      simpa [remainingWork, rootRoundsCost] using
        lastRootRound_evalsInTime completed data
          (by simpa [remainingWork] using workEq) oddEq restoreEq
  | succ additionalRounds induction =>
      let workTail := List.replicate
        (remainingWork (completed + 1) (additionalRounds + 1)) ()
      let nextData : TapeData :=
        { data with
          work := workTail
          odd := List.replicate (2 * (completed + 1) + 1) ()
          oddRestore := []
          root := () :: data.root }
      have splitWork : data.work =
          List.replicate (2 * completed + 1) () ++ workTail := by
        rw [workEq, replicate_remainingWork_succ]
      have throughNext := nextRootRound_evalsInTime completed workTail
        (by simp [workTail, remainingWork]) data splitWork oddEq restoreEq
      have rest := induction (completed + 1) nextData rfl rfl rfl
      have whole := EvalsToInTime.trans (TM2.step program)
        (nextRootRoundCost completed)
        (rootRoundsCost (completed + 1) additionalRounds)
        (consumeWorkCfg data) (consumeWorkCfg nextData)
        (some (clearOddCfg
          { nextData with
            work := []
            odd := []
            oddRestore := List.replicate
              (2 * ((completed + 1) + additionalRounds) + 1) ()
            root := List.replicate (additionalRounds + 1) () ++
              nextData.root }))
        (by simpa [nextData] using throughNext) rest
      have finalOddCount :
          2 * ((completed + 1) + additionalRounds) + 1 =
            2 * (completed + (additionalRounds + 1)) + 1 := by
        omega
      have finalRoot :
          List.replicate (additionalRounds + 1 + 1) () ++ data.root =
            List.replicate (additionalRounds + 1) () ++ () :: data.root := by
        rw [List.replicate_add]
        simp [List.append_assoc]
      convert whole using 1
      · rw [finalRoot, finalOddCount]
      · simp [rootRoundsCost]
        omega

end BoolSquareRowsMachine
end LeanTrominoes
