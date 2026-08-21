/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTimeBound

/-! # Polynomial-time Boolean square-row reshaping -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace BoolSquareRowsMachine

open BoolSquareRows

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 18 * Polynomial.X + Polynomial.C 12

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 18 * length + 12 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Delimiting a promised flat Boolean square into rows is linear time in
the flat input length. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      BoolSquareRows.Input DelimitedBinaryWords.Input
      Bool DelimitedBinaryWords.Token BoolSquareRows.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode BoolSquareRows.Input.delimitedRows where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Bool).invFun
          (BoolSquareRows.finEncoding.encode input))
        (some (List.map (Equiv.refl DelimitedBinaryWords.Token).invFun
          (DelimitedBinaryWords.finEncoding.encode input.delimitedRows)))
        (totalTime input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        BoolSquareRows.finEncoding, DelimitedBinaryWords.finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end BoolSquareRowsMachine
end LeanTrominoes

end
