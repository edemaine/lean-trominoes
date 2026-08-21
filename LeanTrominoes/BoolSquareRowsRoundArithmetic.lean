/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsMachine

/-! # Arithmetic for Boolean square-root counter rounds -/

namespace LeanTrominoes

namespace BoolSquareRowsMachine

/-- Work markers consumed by a given number of successive odd intervals,
starting after `completed` intervals have already been consumed. -/
def remainingWork : Nat → Nat → Nat
  | _, 0 => 0
  | completed, rounds + 1 =>
      2 * completed + 1 + remainingWork (completed + 1) rounds

theorem remainingWork_eq_mul (completed rounds : Nat) :
    remainingWork completed rounds = rounds * (2 * completed + rounds) := by
  induction rounds generalizing completed with
  | zero => simp [remainingWork]
  | succ rounds induction =>
      simp only [remainingWork, induction]
      ring

theorem remainingWork_zero_left (rounds : Nat) :
    remainingWork 0 rounds = rounds ^ 2 := by
  rw [remainingWork_eq_mul]
  simp [pow_two]

theorem replicate_remainingWork_succ (completed rounds : Nat) :
    List.replicate (remainingWork completed (rounds + 1)) () =
      List.replicate (2 * completed + 1) () ++
        List.replicate (remainingWork (completed + 1) rounds) () := by
  simp [remainingWork, List.replicate_add]

end BoolSquareRowsMachine
end LeanTrominoes
