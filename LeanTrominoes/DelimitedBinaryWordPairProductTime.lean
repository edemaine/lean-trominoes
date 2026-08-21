/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTimeBound

/-! # Polynomial-time binary-word ordered product -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordPairProductMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5 * Polynomial.X ^ 2 +
    Polynomial.C 7 * Polynomial.X + Polynomial.C 5

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 5 * length ^ 2 + 7 * length + 5 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow]

/-- Forming every ordered pair of a delimiter-encoded list of arbitrary
binary words is quadratic-time in the complete encoded input length. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWords.Input DelimitedBinaryWordPairs.Input
      WordToken PairToken DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWordPairs.finEncoding.encode pairs where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl WordToken).invFun
          (DelimitedBinaryWords.finEncoding.encode input))
        (some (List.map (Equiv.refl PairToken).invFun
          (DelimitedBinaryWordPairs.finEncoding.encode (pairs input))))
        (totalTime input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        DelimitedBinaryWords.finEncoding,
        DelimitedBinaryWordPairs.finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes

end
