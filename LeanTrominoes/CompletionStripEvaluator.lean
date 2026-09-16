/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCompilerSpace
import LeanTrominoes.PartrecFlatStripDeciderSpace
import LeanTrominoes.PartrecBooleanUniformSpace

/-! # Guarded strip-completion evaluator -/
noncomputable section
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open PeriodicStrip.RawWindowState.FlatStripDeciderPartrec

def Good (t : Tromino) (input : PeriodicStripTrominoPrefill) : Prop :=
  0 < input.height ∧ 0 < input.period ∧ PeriodicStripTrominoPrefill.Valid t input
instance (t : Tromino) (input : PeriodicStripTrominoPrefill) : Decidable (Good t input) := by
  unfold Good
  infer_instance

def guardTest (t : Tromino) : Expr :=
  andE (ltE 0 (var 1)) (andE (ltE 0 (var 2)) (validExpr t))
def guardExpr (t : Tromino) : Expr := .ite (guardTest t) 1 0

theorem guard_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (guardTest t).Truth (fields input) ↔ Good t input := by
  simp only [guardTest,truth_and,truth_lt,eval_var]
  rw [validExpr_truth,valid_iff]
  rfl

theorem guard_eval (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (guardExpr t).eval (fields input) = (decide (Good t input)).toNat := by
  have h := guard_truth t input
  unfold Truth at h
  by_cases hg : Good t input
  · have hn := h.mpr hg
    simp [guardExpr,Expr.eval,hn,hg]
  · have hz : (guardTest t).eval (fields input) = 0 := by tauto
    simp [guardExpr,Expr.eval,hz,hg]

theorem guard_noPower (t : Tromino) : (guardExpr t).noPower = true := by
  simp [guardExpr,guardTest,andE,ltE,Expr.noPower,validExpr_noPower]

def bodyCode (t : Tromino) : Code :=
  (flatPeriodicStripTrominoTilingCode t).comp (Compiler.compileCode t)
def decideCode (t : Tromino) : Code := Code.branchZero (guardExpr t).code Code.zero (bodyCode t)
def result (t : Tromino) (input : PeriodicStripTrominoPrefill) : Bool :=
  decide (Good t input) && flatPeriodicStripTrominoTilingBool t (Compiler.compiledStrip t input)

theorem result_correct (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    result t input = true ↔ problem t input := by
  rw [result,Bool.and_eq_true,decide_eq_true_eq,flatPeriodicStripTrominoTilingBool_eq_true_iff,
    problem_iff_uncovered]
  constructor
  · rintro ⟨⟨hh,hp,hv⟩,ht⟩
    exact ⟨hh,hp,hv,(Compiler.compiled_tiling_iff t input hh hp).mp ht⟩
  · rintro ⟨hh,hp,hv,ht⟩
    exact ⟨⟨hh,hp,hv⟩,(Compiler.compiled_tiling_iff t input hh hp).mpr ht⟩

theorem body_eval (t : Tromino) (input : PeriodicStripTrominoPrefill) (hh : 0 < input.height) :
    (bodyCode t).eval (fields input) =
      pure [(flatPeriodicStripTrominoTilingBool t (Compiler.compiledStrip t input)).toNat] := by
  simp [bodyCode,Compiler.compile_eval t input hh,flatPeriodicStripTrominoTilingCode_eval,Part.bind_eq_bind]
  cases flatPeriodicStripTrominoTilingBool t (Compiler.compiledStrip t input) <;> rfl

theorem decide_eval (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (decideCode t).eval (fields input) = pure [(result t input).toNat] := by
  have guard : (guardExpr t).code.eval (fields input) = pure [(decide (Good t input)).toNat] := by
    rw [Expr.code_eval,guard_eval]
  by_cases hg : Good t input
  · have run := Code.branchZero_eval_succ_at (guardExpr t).code Code.zero (bodyCode t)
      (fields input) 1 (by simpa [hg] using guard) _ (body_eval t input hg.1) (by decide)
    simpa [decideCode,result,hg] using run
  · have run := Code.branchZero_eval_zero_at (guardExpr t).code Code.zero (bodyCode t)
      (fields input) 0 (by simpa [hg] using guard) [0] (by simp) rfl
    simpa [decideCode,result,hg] using run

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
