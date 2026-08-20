/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenParserTimeBound

/-! # Polynomial-time sparse assignment-token expansion -/

namespace LeanTrominoes

open Computability Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 513 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 513 * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le (tromino : Tromino) (tokens : List InputToken) :
    totalTime tromino tokens ≤ timePolynomial.eval tokens.length := by
  rw [timePolynomial_eval]
  have outputBound := expand_length_le_scanTime tromino tokens
  have scanBound := scanTime_start_le tromino tokens
  have squarePositive : 1 ≤ (tokens.length + 1) ^ 2 := by
    nlinarith [Nat.zero_le tokens.length]
  unfold totalTime
  omega

/-- Expanding finite unary assignment records into prepared affine pixel
tokens is polynomial-time (quadratic on arbitrary, possibly malformed words). -/
noncomputable def computableInPolyTime (tromino : Tromino) :
    @TM2ComputableInPolyTime
      (List InputToken) (List OutputToken) InputToken OutputToken id id
      (GadgetSparseAssignmentTokens.expand tromino) where
  tm := machine tromino
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun tokens := by
    have run := machine_outputsInTime tromino tokens
    have run' : TM2OutputsInTime (machine tromino)
        (List.map (Equiv.refl InputToken).invFun (id tokens))
        (some (List.map (Equiv.refl OutputToken).invFun
          (id (GadgetSparseAssignmentTokens.expand tromino tokens))))
        (totalTime tromino tokens) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (totalTime_le tromino tokens) }

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
