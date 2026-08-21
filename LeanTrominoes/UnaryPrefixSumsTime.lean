/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsInterface
import LeanTrominoes.UnaryPrefixSumsTimeBound

/-! # Polynomial-time unary prefix sums -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace UnaryPrefixSumsMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 5 * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

/-- Stable unary block starts are computable in quadratic time in the complete
delimiter encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Nat) (List Nat) Symbol Symbol
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields
      PrefixSums.starts where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun values := by
    have run := machine_outputsInTime values
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Symbol).invFun
          (UnaryFieldEncoderMachine.unaryFields values))
        (some (List.map (Equiv.refl Symbol).invFun
          (UnaryFieldEncoderMachine.unaryFields
            (PrefixSums.starts values))))
        (totalTime values) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le values) }

end UnaryPrefixSumsMachine
end LeanTrominoes

end
