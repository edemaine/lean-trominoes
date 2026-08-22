/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapFullExecution

/-! # Polynomial envelope for end-delimited block maps -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

section

variable {Source Target : Type}
variable {function : List Source → List Target}

def unitCost (inner : TM2ComputableInPolyTime id id function)
    (length : Nat) : Nat :=
  inner.time.eval length +
    4 * (TM2OutputLength.outputLengthPolynomial inner).eval length +
    2 * length + Fintype.card inner.tm.K + 5

def unitCostPolynomial
    (inner : TM2ComputableInPolyTime id id function) : Polynomial Nat :=
  inner.time +
    Polynomial.C 4 * TM2OutputLength.outputLengthPolynomial inner +
    Polynomial.C 2 * Polynomial.X +
    Polynomial.C (Fintype.card inner.tm.K + 5)

@[simp] theorem unitCostPolynomial_eval
    (inner : TM2ComputableInPolyTime id id function) (length : Nat) :
    (unitCostPolynomial inner).eval length = unitCost inner length := by
  simp [unitCostPolynomial, unitCost, Polynomial.eval_add,
    Polynomial.eval_mul]
  omega

def mapTimePolynomial
    (inner : TM2ComputableInPolyTime id id function) : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) * unitCostPolynomial inner

@[simp] theorem mapTimePolynomial_eval
    (inner : TM2ComputableInPolyTime id id function) (length : Nat) :
    (mapTimePolynomial inner).eval length =
      (length + 1) * unitCost inner length := by
  simp [mapTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Polynomials over natural coefficients are monotone on natural inputs. -/
theorem polynomialEvalMonotone (polynomial : Polynomial Nat) :
    Monotone polynomial.eval := by
  intro smaller larger bound
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add leftInduction rightInduction
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient
        (Nat.pow_le_pow_left bound degree)

theorem unitCost_three_le
    (inner : TM2ComputableInPolyTime id id function) (length : Nat) :
    3 ≤ unitCost inner length := by
  unfold unitCost
  omega

/-- The per-symbol unit pays for a complete block, including the additional
reverse-output population carried into the recursive suffix run. -/
theorem blockRunTime_with_output_le_unitCost
    (inner : TM2ComputableInPolyTime id id function)
    (block : List Source) (limit : Nat)
    (lengthBound : block.length ≤ limit) :
    2 * (function block).length + (blockRunTime inner block + 2) ≤
      unitCost inner limit := by
  have timeBound : inner.time.eval block.length ≤
      inner.time.eval limit :=
    polynomialEvalMonotone inner.time lengthBound
  have rawOutputBound :=
    TM2OutputLength.output_length_le_polynomial_eval inner block
  have outputMonotone :
      (TM2OutputLength.outputLengthPolynomial inner).eval block.length ≤
        (TM2OutputLength.outputLengthPolynomial inner).eval limit :=
    polynomialEvalMonotone
      (TM2OutputLength.outputLengthPolynomial inner) lengthBound
  have outputBound : (function block).length ≤
      (TM2OutputLength.outputLengthPolynomial inner).eval limit := by
    exact rawOutputBound.trans outputMonotone
  unfold blockRunTime unitCost
  omega

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
