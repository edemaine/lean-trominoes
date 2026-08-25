/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessTimeBound

/-! # Polynomial-time unary word-pair excesses -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 3 * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Cancelling the two words in every delimiter-encoded pair and retaining
the selected excess is linear-time in the complete encoded input length. -/
noncomputable def computableInPolyTime (keepFirst : Bool) :
    @TM2ComputableInPolyTime
      Input (List Nat) Token UnaryFieldEncoderMachine.Symbol
      finEncoding.encode UnaryFieldEncoderMachine.unaryFields
      (excesses keepFirst) where
  tm := machine keepFirst
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime keepFirst input
    have run' : TM2OutputsInTime (machine keepFirst)
        (List.map (Equiv.refl Token).invFun (finEncoding.encode input))
        (some (List.map
          (Equiv.refl UnaryFieldEncoderMachine.Symbol).invFun
          (UnaryFieldEncoderMachine.unaryFields (excesses keepFirst input))))
        (totalTime keepFirst input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le keepFirst input) }

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes

end
