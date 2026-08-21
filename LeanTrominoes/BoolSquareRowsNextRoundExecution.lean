/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCounterCleanupExecution
import LeanTrominoes.BoolSquareRowsOddIntervalExecution

/-! # Nonfinal square-root counter round -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def nextRootRoundCost (completed : Nat) : Nat :=
  4 * (2 * completed + 1) + 2

/-- A complete nonfinal odd interval increments the root, restores an odd
counter two markers longer, and returns to the work-consumption loop. -/
def nextRootRound_evalsInTime (completed : Nat) (workTail : List Unit)
    (workTailNe : workTail ≠ []) (data : TapeData)
    (workEq : data.work =
      List.replicate (2 * completed + 1) () ++ workTail)
    (oddEq : data.odd = List.replicate (2 * completed + 1) ())
    (restoreEq : data.oddRestore = []) :
    EvalsToInTime (TM2.step program) (consumeWorkCfg data)
      (some (consumeWorkCfg
        { data with
          work := workTail
          odd := List.replicate (2 * (completed + 1) + 1) ()
          oddRestore := []
          root := () :: data.root }))
      (nextRootRoundCost completed) := by
  let odd := List.replicate (2 * completed + 1) ()
  let afterOdd : TapeData :=
    { data with
      work := workTail
      odd := []
      oddRestore := odd.reverse ++ data.oddRestore }
  have throughOdd := oddInterval_evalsInTime odd workTail
    (by simp [odd]) data (by simpa [odd] using workEq) oddEq
  cases workTail with
  | nil => exact (workTailNe rfl).elim
  | cons marker tail =>
      rcases marker with ⟨⟩
      let afterFinish : TapeData :=
        { afterOdd with root := () :: afterOdd.root }
      have finish := oneStep
        (step_finishRootStep_cons afterOdd tail rfl)
      have throughFinish := EvalsToInTime.trans (TM2.step program)
        (3 * odd.length) 1
        (consumeWorkCfg data) (finishRootStepCfg afterOdd)
        (some (restoreOddCfg afterFinish))
        (by simpa [afterOdd] using throughOdd)
        (by simpa [afterFinish] using finish)
      have restored := restoreOdd_evalsInTime odd.reverse afterFinish
        (by simp [afterFinish, afterOdd, restoreEq])
      have whole := EvalsToInTime.trans (TM2.step program)
        (1 + 3 * odd.length) (odd.reverse.length + 1)
        (consumeWorkCfg data) (restoreOddCfg afterFinish)
        (some (consumeWorkCfg
          { afterFinish with
            odd := () :: () :: odd.reverse.reverse ++ afterFinish.odd
            oddRestore := [] }))
        (by simpa using throughFinish) restored
      have nextOdd :
          List.replicate (2 * (completed + 1) + 1) () =
            () :: () :: List.replicate (2 * completed + 1) () := by
        rw [show 2 * (completed + 1) + 1 =
          2 + (2 * completed + 1) by omega, List.replicate_add]
        rfl
      convert whole using 1
      · simp [afterFinish, afterOdd, odd, nextOdd]
      · simp [nextRootRoundCost, odd]
        omega

end BoolSquareRowsMachine
end LeanTrominoes
