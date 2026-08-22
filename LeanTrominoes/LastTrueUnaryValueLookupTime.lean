/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupInterface
import LeanTrominoes.LastTrueUnaryValueLookupTimeBound

/-! # Polynomial-time last-true unary lookup -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace LastTrueUnaryValueLookupMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 20 *
    (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1)

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 20 * (length ^ 2 + length + 1) := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

/-- Looking up the unary value at every row's last true position is
computable in quadratic time in the complete separated encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnarySymbol
      encode UnaryFieldEncoderMachine.unaryFields
      (fun input => lookups input.rows input.values) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl InputSymbol).invFun (encode input))
        (some (List.map (Equiv.refl UnarySymbol).invFun
          (UnaryFieldEncoderMachine.unaryFields
            (lookups input.rows input.values))))
        (totalTime input) := by
      simpa only [outputEncoding,
        FiniteBlockTransducer.map_refl_invFun] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end LastTrueUnaryValueLookupMachine
end LeanTrominoes

end
