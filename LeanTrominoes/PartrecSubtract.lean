/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecListCode

/-!
# Explicit partial-recursive truncated subtraction

This module implements `minuend - subtrahend` as a flat countdown that
repeatedly applies predecessor to a singleton payload.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

def subtractStepList (values : List Nat) : List Nat :=
  [values.headI.pred]

@[simp]
theorem pred_eval_named (values : List Nat) :
    pred.eval values = pure (subtractStepList values) := by
  simp [subtractStepList]

theorem subtractStepList_iterate
    (steps value : Nat) :
    ((subtractStepList)^[steps]) [value] =
      [value - steps] := by
  induction steps with
  | zero =>
      simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, subtractStepList]
      omega

/-- Reorder `[minuend, subtrahend]` into a countdown and payload. -/
def subtractInputCode : Code :=
  prepend (get 1) (get 0)

@[simp]
theorem subtractInputCode_eval
    (minuend subtrahend : Nat) :
    subtractInputCode.eval [minuend, subtrahend] =
      pure [subtrahend, minuend] := by
  simp [subtractInputCode]

/-- Binary explicit code for truncated natural subtraction. -/
def subtractCode : Code :=
  (flatIterate pred).comp subtractInputCode

@[simp]
theorem subtractCode_eval
    (minuend subtrahend : Nat) :
    subtractCode.eval [minuend, subtrahend] =
      pure [minuend - subtrahend] := by
  calc
    _ = (flatIterate pred).eval [subtrahend, minuend] := by
      simp [subtractCode]
    _ = pure (((subtractStepList)^[subtrahend]) [minuend]) :=
      flatIterate_eval pred subtractStepList
        pred_eval_named subtrahend [minuend]
    _ = _ := by rw [subtractStepList_iterate]

end Turing.ToPartrec.Code
