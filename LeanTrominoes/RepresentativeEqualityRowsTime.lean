/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsInterface
import LeanTrominoes.RepresentativeEqualityRowsTimeBound

/-! # Polynomial-time stable representative-row filtering -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace RepresentativeEqualityRowsMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5 * Polynomial.X ^ 2 +
    Polynomial.C 7 * Polynomial.X + Polynomial.C 3

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 5 * length ^ 2 + 7 * length + 3 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow]

/-- Stable first-occurrence representative filtering is quadratic time in
the complete delimiter encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWords.Input DelimitedBinaryWords.Input
      DelimitedBinaryWords.Token DelimitedBinaryWords.Token
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode
      RepresentativeEqualityRows.rows where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl DelimitedBinaryWords.Token).invFun
          (DelimitedBinaryWords.finEncoding.encode input))
        (some (List.map (Equiv.refl DelimitedBinaryWords.Token).invFun
          (DelimitedBinaryWords.finEncoding.encode
            (RepresentativeEqualityRows.rows input))))
        (totalTime input.words) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        DelimitedBinaryWords.finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end RepresentativeEqualityRowsMachine
end LeanTrominoes

end
