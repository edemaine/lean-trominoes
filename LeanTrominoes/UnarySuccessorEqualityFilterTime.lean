/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterInterface
import LeanTrominoes.UnarySuccessorEqualityFilterTimeBound

/-! # Polynomial-time unary successor-equality filtering -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace UnarySuccessorEqualityFilterMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * (Polynomial.X + Polynomial.C 1)

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 12 * (length + 1) := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add]

/-- Filtering aligned unary rank/size streams by successor equality is
computable in linear time in their complete separated encoding. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnarySymbol
      encode UnaryFieldEncoderMachine.unaryFields
      (fun input => selectedValues input.ranks input.sizes) where
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
            (selectedValues input.ranks input.sizes))))
        (totalTime input) := by
      simpa only [outputEncoding,
        FiniteBlockTransducer.map_refl_invFun] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (by
          rw [timePolynomial_eval]
          exact totalTime_le input) }

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes

end
