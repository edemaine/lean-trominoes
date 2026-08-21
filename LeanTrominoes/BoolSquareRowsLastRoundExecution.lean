/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsOddIntervalExecution

/-! # Final square-root counter round -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def lastRootRoundCost (completed : Nat) : Nat :=
  3 * (2 * completed + 1) + 1

/-- The last complete odd interval increments the root and enters cleanup. -/
def lastRootRound_evalsInTime (completed : Nat) (data : TapeData)
    (workEq : data.work = List.replicate (2 * completed + 1) ())
    (oddEq : data.odd = List.replicate (2 * completed + 1) ())
    (restoreEq : data.oddRestore = []) :
    EvalsToInTime (TM2.step program) (consumeWorkCfg data)
      (some (clearOddCfg
        { data with
          work := []
          odd := []
          oddRestore := List.replicate (2 * completed + 1) ()
          root := () :: data.root }))
      (lastRootRoundCost completed) := by
  let odd := List.replicate (2 * completed + 1) ()
  let afterOdd : TapeData :=
    { data with
      work := []
      odd := []
      oddRestore := odd.reverse ++ data.oddRestore }
  have throughOdd := oddInterval_evalsInTime odd [] (by simp [odd]) data
    (by simp [odd, workEq]) oddEq
  have finish := oneStep (step_finishRootStep_nil afterOdd rfl)
  have composed := EvalsToInTime.trans (TM2.step program)
    (3 * odd.length) 1
    (consumeWorkCfg data) (finishRootStepCfg afterOdd)
    (some (clearOddCfg
      { afterOdd with
        work := []
        root := () :: afterOdd.root }))
    (by simpa [afterOdd] using throughOdd) finish
  convert composed using 1
  · simp [afterOdd, odd, restoreEq]
  · simp [lastRootRoundCost, odd]
    omega

end BoolSquareRowsMachine
end LeanTrominoes
