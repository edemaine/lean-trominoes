/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddTapes

/-! # Shared execution lemmas for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

theorem replicate_unit_cons_comm (count : Nat) (tail : List UnarySymbol) :
    List.replicate count (.unit : UnarySymbol) ++ .unit :: tail =
      .unit :: (List.replicate count (.unit : UnarySymbol) ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

end UnaryAlignedAddMachine
end LeanTrominoes
