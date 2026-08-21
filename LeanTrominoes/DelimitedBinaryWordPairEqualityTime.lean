/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityTimeBound

/-! # Polynomial-time delimited binary-word equality -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 3 * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Comparing a delimiter-encoded list of arbitrary binary-word pairs is
linear-time in the complete encoded word length. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      Input (List Bool) Token Bool finEncoding.encode id equalities where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Token).invFun (finEncoding.encode input))
        (some (List.map (Equiv.refl Bool).invFun
          (id (equalities input))))
        (totalTime input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq,
        finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes

end
