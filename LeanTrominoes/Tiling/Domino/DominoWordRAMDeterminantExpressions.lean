/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitExpressionCorrectness
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Fixed arithmetic circuits for determinants and Cramer numerators

For each fixed dimension these are finite expressions in the original matrix
and vector entries. Leibniz sums are unrolled in the program, and their integer
arithmetic is executed by the checked binary-array routines.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit

variable {arity d : ℕ}

def Expression.sum : List (Expression arity) → Expression arity
  | [] => .constant false
  | e::es => .arithmetic .add e (Expression.sum es)

def Expression.product : List (Expression arity) → Expression arity
  | [] => .constant true
  | e::es => .arithmetic .mul e (Expression.product es)

theorem Expression.eval_sum {R : Type} [Ring R] (inputs : Fin arity → R) (es : List (Expression arity)) :
    (Expression.sum es).eval inputs=(es.map (Expression.eval inputs)).sum := by
  induction es <;> simp_all [Expression.sum,Expression.eval,Operation.eval,bitValue]

theorem Expression.eval_product {R : Type} [Ring R] (inputs : Fin arity → R) (es : List (Expression arity)) :
    (Expression.product es).eval inputs=(es.map (Expression.eval inputs)).prod := by
  induction es <;> simp_all [Expression.product,Expression.eval,Operation.eval,bitValue]

def signedExpression (σ : Equiv.Perm (Fin d)) (e : Expression arity) : Expression arity :=
  if (Equiv.Perm.sign σ : ℤ)=1 then e else .arithmetic .sub (.constant false) e

theorem eval_signedExpression {R : Type} [Ring R] (inputs : Fin arity → R)
    (σ : Equiv.Perm (Fin d)) (e : Expression arity) :
    (signedExpression σ e).eval inputs=((Equiv.Perm.sign σ : ℤ) : R)*e.eval inputs := by
  have unit : IsUnit (Equiv.Perm.sign σ : ℤ) := (Equiv.Perm.sign σ).isUnit
  rcases Int.isUnit_iff.mp unit with sign | sign <;>
    simp [signedExpression,sign,Expression.eval,Operation.eval,bitValue]

noncomputable def determinantExpression (A : Matrix (Fin d) (Fin d) (Expression arity)) : Expression arity :=
  Expression.sum ((Finset.univ.toList : List (Equiv.Perm (Fin d))).map fun σ =>
    signedExpression σ (Expression.product ((Finset.univ.toList : List (Fin d)).map fun i => A (σ i) i)))

/-- The unrolled expression computes the mathematical determinant over any
commutative ring, including integers and residues modulo binary precision. -/
theorem eval_determinantExpression {R : Type} [CommRing R] (inputs : Fin arity → R)
    (A : Matrix (Fin d) (Fin d) (Expression arity)) :
    (determinantExpression A).eval inputs=Matrix.det (fun i j => (A i j).eval inputs : Matrix (Fin d) (Fin d) R) := by
  simp only [determinantExpression,Expression.eval_sum,List.map_map,Function.comp_def,
    eval_signedExpression,Expression.eval_product,Finset.prod_map_toList,Finset.sum_map_toList,
    Matrix.det_apply']

def replacementExpression (A : Matrix (Fin d) (Fin d) (Expression arity)) (i j : Fin d) :
    Matrix (Fin d) (Fin d) (Expression arity) :=
  fun row col => if row=j then (if col=i then .constant true else .constant false) else A row col

noncomputable def adjugateExpression (A : Matrix (Fin d) (Fin d) (Expression arity)) (i j : Fin d) :
    Expression arity := determinantExpression (replacementExpression A i j)

theorem eval_adjugateExpression {R : Type} [CommRing R] (inputs : Fin arity → R)
    (A : Matrix (Fin d) (Fin d) (Expression arity)) (i j : Fin d) :
    (adjugateExpression A i j).eval inputs=
      Matrix.adjugate (fun a b => (A a b).eval inputs : Matrix (Fin d) (Fin d) R) i j := by
  rw [adjugateExpression,eval_determinantExpression,Matrix.adjugate_apply]
  congr 1
  funext row col
  by_cases hr : row=j <;> by_cases hc : col=i <;>
    simp [replacementExpression,Matrix.updateRow_apply,Pi.single_apply,hr,hc,Expression.eval,bitValue]

noncomputable def numeratorExpression (A : Matrix (Fin d) (Fin d) (Expression arity))
    (x : Fin d → Expression arity) (i : Fin d) : Expression arity :=
  Expression.sum ((Finset.univ.toList : List (Fin d)).map fun j =>
    .arithmetic .mul (adjugateExpression A i j) (x j))

theorem eval_numeratorExpression {R : Type} [CommRing R] (inputs : Fin arity → R)
    (A : Matrix (Fin d) (Fin d) (Expression arity)) (x : Fin d → Expression arity) (i : Fin d) :
    (numeratorExpression A x i).eval inputs=
      Matrix.mulVec (Matrix.adjugate (fun a b => (A a b).eval inputs : Matrix (Fin d) (Fin d) R))
        (fun j => (x j).eval inputs) i := by
  simp only [numeratorExpression,Expression.eval_sum,List.map_map,Function.comp_def,
    Expression.eval,Operation.eval,eval_adjugateExpression,Finset.sum_map_toList,Matrix.mulVec,dotProduct]

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
