/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsDropLastExecution
import LeanTrominoes.FiniteBlockTransducer

/-! # Polynomial time for final delimited-binary-word removal -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordsDropLastMachine

/-- Semantic removal of the final delimited binary word. -/
def dropLast (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.dropLast⟩

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 2 * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Removing the final delimiter-separated binary word is linear time. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWords.Input DelimitedBinaryWords.Input
      DelimitedBinaryWords.Token DelimitedBinaryWords.Token
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode dropLast where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Token).invFun
          (DelimitedBinaryWords.finEncoding.encode input))
        (some (List.map (Equiv.refl Token).invFun
          (DelimitedBinaryWords.finEncoding.encode (dropLast input))))
        (2 * (DelimitedBinaryWords.encode input).length + 2) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        DelimitedBinaryWords.finEncoding, dropLast] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          rfl) }

end DelimitedBinaryWordsDropLastMachine
end LeanTrominoes

end
