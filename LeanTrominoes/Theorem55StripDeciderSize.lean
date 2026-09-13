/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripDecider

/-! # Quadratic state and recursion-depth bounds in the actual strip input length -/

namespace LeanTrominoes.Theorem55StripEncoding

theorem unaryFields_length (values : List Nat) : (unaryFields values).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    simp only [unaryFields,List.flatMap_cons,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil,List.sum_cons] at *
    omega

theorem encoding_length (input : Theorem55.StripInput) :
    (finEncoding.encode input).length = (fields input).sum + (fields input).length :=
  unaryFields_length _

theorem height_le_encoding_length (input : Theorem55.StripInput) :
    input.1 ≤ (finEncoding.encode input).length := by
  rw [encoding_length]
  simp only [fields,List.sum_append,List.sum_cons,List.sum_nil]
  omega

end LeanTrominoes.Theorem55StripEncoding

namespace LeanTrominoes.Theorem55StripDecider

theorem bound_le_encoding_length (input : Theorem55.StripInput) :
    bound input ≤ (Theorem55StripEncoding.finEncoding.encode input).length + 7 := by
  rw [Theorem55StripEncoding.encoding_length]
  unfold bound
  omega

noncomputable def statePolynomial : Polynomial Nat :=
  Polynomial.C 16 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 15) *
    (Polynomial.C 3 * Polynomial.X + Polynomial.C 15)

@[simp] theorem statePolynomial_eval (length : Nat) :
    statePolynomial.eval length = 16*(2*length+15)*(3*length+15) := by
  simp [statePolynomial]

/-- A window can be represented by quadratically many bits of the original input. -/
theorem stateBits_le (input : Theorem55.StripInput) :
    PolyominoStripWindow.stateBits Bool input.1 (bound input) ≤
      statePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length := by
  have hb := bound_le_encoding_length input
  have hh := Theorem55StripEncoding.height_le_encoding_length input
  rw [statePolynomial_eval]
  calc
    _ = 16*(2*bound input+1)*(input.1+2*bound input+1) := by
      simp [PolyominoStripWindow.stateBits]
      ring
    _ ≤ 16*(2*(Theorem55StripEncoding.finEncoding.encode input).length+15)*
        (3*(Theorem55StripEncoding.finEncoding.encode input).length+15) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 16 (by omega)) (by omega)

/-- The verified reachability recursion has polynomial depth as well. -/
theorem savitchDepth_le (input : Theorem55.StripInput) :
    FiniteState.savitchDepth (PolyominoStripWindow.Window Bool input.1 (bound input)) ≤
      statePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length + 1 := by
  rw [PolyominoStripWindow.savitchDepth_window]
  exact Nat.add_le_add_right (stateBits_le input) 1

end LeanTrominoes.Theorem55StripDecider
