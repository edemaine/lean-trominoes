/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCountSteps

/-! # Exact odd intervals of the Boolean square-root counter -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

/-- Consuming one complete nonempty odd interval takes three machine steps
per work marker and leaves the interval on the restore stack. -/
def oddInterval_evalsInTime (odd workTail : List Unit)
    (oddNe : odd ≠ []) (data : TapeData)
    (workEq : data.work = odd ++ workTail)
    (oddEq : data.odd = odd) :
    EvalsToInTime (TM2.step program) (consumeWorkCfg data)
      (some (finishRootStepCfg
        { data with
          work := workTail
          odd := []
          oddRestore := odd.reverse ++ data.oddRestore }))
      (3 * odd.length) := by
  induction odd generalizing data with
  | nil => exact (oddNe rfl).elim
  | cons marker odd induction =>
      rcases marker with ⟨⟩
      let afterWork : TapeData :=
        { data with work := odd ++ workTail }
      let afterOdd : TapeData :=
        { afterWork with
          odd := odd
          oddRestore := () :: data.oddRestore }
      have consumedWork := oneStep
        (step_consumeWork_cons data (odd ++ workTail) (by
          simp [workEq]))
      have consumedOdd := oneStep
        (step_consumeOdd_cons afterWork odd (by
          simp [afterWork, oddEq]))
      have firstTwo := EvalsToInTime.trans (TM2.step program)
        1 1
        (consumeWorkCfg data) (consumeOddCfg afterWork)
        (some (checkOddCfg afterOdd))
        (by simpa [afterWork] using consumedWork)
        (by simpa [afterOdd] using consumedOdd)
      cases odd with
      | nil =>
          have checked := oneStep (step_checkOdd_nil afterOdd rfl)
          have composed := EvalsToInTime.trans (TM2.step program)
            2 1
            (consumeWorkCfg data) (checkOddCfg afterOdd)
            (some (finishRootStepCfg { afterOdd with odd := [] }))
            (by simpa using firstTwo) checked
          convert composed using 1
          · simp [afterOdd, afterWork]
          · simp
      | cons next rest =>
          let afterCheck : TapeData :=
            { afterOdd with odd := () :: rest }
          have checked := oneStep
            (step_checkOdd_cons afterOdd rest rfl)
          have firstThree := EvalsToInTime.trans (TM2.step program)
            2 1
            (consumeWorkCfg data) (checkOddCfg afterOdd)
            (some (consumeWorkCfg afterCheck))
            (by simpa using firstTwo)
            (by simpa [afterCheck] using checked)
          have remaining := induction (by simp) afterCheck
            (by simp [afterCheck, afterOdd, afterWork]) rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            3 (3 * (List.length (next :: rest)))
            (consumeWorkCfg data) (consumeWorkCfg afterCheck)
            (some (finishRootStepCfg
              { afterCheck with
                work := workTail
                odd := []
                oddRestore :=
                  (next :: rest).reverse ++ afterCheck.oddRestore }))
            (by simpa using firstThree) remaining
          convert composed using 1
          · simp [afterCheck, afterOdd, afterWork, List.reverse_cons,
              List.append_assoc]
          · simp
            omega

end BoolSquareRowsMachine
end LeanTrominoes
