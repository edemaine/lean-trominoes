/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterExecution
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterLength
import LeanTrominoes.FiniteBlockTransducer

/-! # Polynomial time for Boolean filtering of binary-word pairs -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordPairBooleanFilterMachine

open DelimitedBinaryWordPairBooleanFilter

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 3 * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- A dynamically sized Boolean mask filters a delimited pair
stream in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeInput
      DelimitedBinaryWordPairs.encode output where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have pairCountBound := pairs_length_le_encode_length input.pairs
    have selectedLengthBound :=
      selectedPairs_encode_length_le input.controls input.pairs
    refine
      { steps := run.steps
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · simpa only [FiniteBlockTransducer.map_refl_invFun, output] using
        run.evals_in_steps
    · exact run.steps_le_m.trans (by
        rw [timePolynomial_eval, encodeInput_length]
        omega)

end DelimitedBinaryWordPairBooleanFilterMachine
end LeanTrominoes

end
