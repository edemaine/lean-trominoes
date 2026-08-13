/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPolySpace

/-!
# Tail-style iteration in the partial-recursive evaluator

`ToPartrec.Code.prec` is already implemented using `fix`, but this module
records the list-shaped loop needed by the flat Savitch evaluator.  Its state
is `remaining :: payload`; each positive iteration applies a supplied code to
the payload and decrements `remaining`.  The loop is tail-style, so the
evaluator does not retain one continuation per iteration.
-/

namespace Turing.ToPartrec.Code

/-- Constant singleton output `[1]`. -/
def one : Code :=
  succ.comp zero

@[simp]
theorem one_eval (values : List Nat) :
    one.eval values = pure [1] := by
  simp [one]

/-- Body of a countdown loop.  At zero it emits a zero exit tag followed by
the payload.  At a successor it emits a positive continue tag, the predecessor
counter, and the transformed payload. -/
def flatCountdownBody (stepCode : Code) : Code :=
  case zero' <|
    cons one <|
      cons head <|
        stepCode.comp tail

theorem flatCountdownBody_zero_eval (stepCode : Code)
    (payload : List Nat) :
    (flatCountdownBody stepCode).eval (0 :: payload) =
      pure (0 :: payload) := by
  simp [flatCountdownBody]

theorem flatCountdownBody_succ_eval
    (stepCode : Code) (step : List Nat → List Nat)
    (stepCorrect : ∀ payload, stepCode.eval payload = pure (step payload))
    (remaining : Nat) (payload : List Nat) :
    (flatCountdownBody stepCode).eval ((remaining + 1) :: payload) =
      pure (1 :: remaining :: step payload) := by
  simp [flatCountdownBody, stepCorrect]

/-- Apply `stepCode` to a flat payload exactly the number of times stored in
the leading counter. -/
def flatIterate (stepCode : Code) : Code :=
  fix (flatCountdownBody stepCode)

theorem flatIterate_eval
    (stepCode : Code) (step : List Nat → List Nat)
    (stepCorrect : ∀ payload, stepCode.eval payload = pure (step payload))
    (steps : Nat) (payload : List Nat) :
    (flatIterate stepCode).eval (steps :: payload) =
      pure ((step^[steps]) payload) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing payload with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨steps :: step payload, ?_, ?_⟩
      · simp [flatCountdownBody_succ_eval _ step stepCorrect]
      · simpa [Function.iterate_succ_apply] using
          induction (step payload)

end Turing.ToPartrec.Code
