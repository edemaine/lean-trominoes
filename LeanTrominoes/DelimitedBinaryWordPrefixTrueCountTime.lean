/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountInterface
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTimeBound

/-! # Polynomial-time row-prefix true counts -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 7 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 7 * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWords.Input (List Nat)
      Token OutputSymbol
      DelimitedBinaryWords.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields
      DelimitedBinaryWordPrefixTrueCounts.counts where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    have run := machine_outputsInTime input
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Token).invFun
          (DelimitedBinaryWords.finEncoding.encode input))
        (some (List.map (Equiv.refl OutputSymbol).invFun
          (UnaryFieldEncoderMachine.unaryFields
            (DelimitedBinaryWordPrefixTrueCounts.counts input))))
        (totalTime input.words) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        DelimitedBinaryWords.finEncoding] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input.words) }

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes

end
