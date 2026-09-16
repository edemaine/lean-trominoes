/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripEvaluator

/-! # Polynomial-space certificate for the strip-completion evaluator -/
noncomputable section
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open PeriodicStrip.RawWindowState.FlatStripDeciderPartrec

def compilerPolynomial (t : Tromino) : Polynomial Nat :=
  Polynomial.C (Compiler.compileCoefficient t)*(Polynomial.X+1)^5

def bodyPolynomial (t : Tromino) : Polynomial Nat :=
  flatPeriodicStripTrominoTilingSpacePolynomial.comp (compilerPolynomial t)+compilerPolynomial t

def guardCoefficient (t : Tromino) : Nat := (guardExpr t).weight*((guardExpr t).radius+1)

def spacePolynomial (t : Tromino) : Polynomial Nat :=
  Polynomial.C (guardCoefficient t)*(3*Polynomial.X+6)+bodyPolynomial t+
    10000*(3*Polynomial.X+6)+100*(3*Polynomial.X+7)

private theorem eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

theorem body_fits (t : Tromino) (input : PeriodicStripTrominoPrefill) (hh : 0 < input.height) :
    EvaluatorCodeFits (bodyCode t) (fields input)
      [(flatPeriodicStripTrominoTilingBool t (Compiler.compiledStrip t input)).toNat]
      ((bodyPolynomial t).eval (CompletionStripEncoding.finEncoding.encode input).length) := by
  let n := (CompletionStripEncoding.finEncoding.encode input).length
  have compiler := (Compiler.compile_fits t input hh).mono (Compiler.compileBudget_polynomial t input)
  have compiledLength : (PeriodicStripFlatEncoding.finEncoding.encode (Compiler.compiledStrip t input)).length ≤
      (compilerPolynomial t).eval n := by
    have h := compiler.output_space
    simpa [PeriodicStripFlatEncoding.finEncoding_encode_length,encodedListSpace_eq_sum,
      compilerPolynomial,n] using h
  have decider := (flatPeriodicStripTrominoTiling_fits_polynomial t (Compiler.compiledStrip t input)).mono
    (eval_mono flatPeriodicStripTrominoTilingSpacePolynomial compiledLength)
  have total := comp decider compiler
  have boolEncode (b : Bool) : Encodable.encode b = b.toNat := by cases b <;> rfl
  simp only [boolEncode] at total
  simpa [bodyCode,bodyPolynomial,Polynomial.eval_comp,compilerPolynomial,n] using total

theorem decide_fits (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    EvaluatorCodeFits (decideCode t) (fields input) [(result t input).toNat]
      ((spacePolynomial t).eval (CompletionStripEncoding.finEncoding.encode input).length) := by
  have guard := (guardExpr t).code_fits_automatic (fields input) (guard_noPower t)
  rw [guard_eval] at guard
  have body : decide (Good t input) = true → EvaluatorCodeFits (bodyCode t) (fields input)
      [(flatPeriodicStripTrominoTilingBool t (Compiler.compiledStrip t input)).toNat]
      ((bodyPolynomial t).eval (CompletionStripEncoding.finEncoding.encode input).length) :=
    fun hg => body_fits t input (of_decide_eq_true hg).1
  have total := guard_bool guard body
  apply total.mono
  have raw := Compiler.raw_space_le input
  have test := Nat.mul_le_mul_left (guardCoefficient t) (Nat.add_le_add_right raw 1)
  simp only [guardBudget,spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_X,guardCoefficient] at test ⊢
  simp only [Nat.add_assoc,show (5:Nat)+1=6 from rfl] at test
  omega

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
