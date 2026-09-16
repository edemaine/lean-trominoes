/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCompilerCode
import LeanTrominoes.CompletionStripCompilerBounds

/-! # Evaluator workspace for the rectangular scan -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def stepCoefficient (t : Tromino) : Nat :=
  4*((wordExpr t).weight*((wordExpr t).radius+1)+
    4*((countExpr t).weight*((countExpr t).radius+1)+
      4*((var 2+1).weight*((var 2+1).radius+1)+40000+1)+1)+1)

theorem step_fits (t : Tromino) (values : List Nat) :
    EvaluatorCodeFits (stepCode t) values (step t values)
      (stepCoefficient t*(encodedListSpace values+1)) := by
  have result := prepend_linear ((wordExpr t).code_fits_automatic values (word_noPower t))
    (prepend_linear ((countExpr t).code_fits_automatic values (count_noPower t))
      (prepend_linear ((var 2+1).code_fits_automatic values (by simp [Expr.noPower])) (drop_linear 3 values)))
  change EvaluatorCodeFits (stepCode t) values _ (stepCoefficient t*(encodedListSpace values+1)) at result
  have eq : (wordExpr t).eval values :: (countExpr t).eval values ::
      (var 2+1).eval values :: values.drop 3 = step t values := by
    by_cases h : (testExpr t).eval values = 0 <;>
      simp [wordExpr,countExpr,appendedExpr,baseExpr,step,Expr.eval,Op.eval,var,h]
  rw [eq] at result
  exact result

theorem scan_fits (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) :
    EvaluatorCodeFits (Code.flatIterate (stepCode t))
      ((input.period*input.height)::([0,0,0]++fields input))
      (payload t input (input.period*input.height))
      (iterationBudget (stepCoefficient t*(scanSpace input+1))
        (Computability.encodeNat (input.period*input.height)).length) := by
  have steps (taken : Nat) (ht : taken ≤ input.period*input.height) :
      EvaluatorCodeFits (stepCode t) ((step t)^[taken] ([0,0,0]++fields input))
        ((step t)^[taken+1] ([0,0,0]++fields input))
        (stepCoefficient t*(scanSpace input+1)) := by
    rw [Function.iterate_succ_apply',iterate_payload]
    exact (step_fits t _).mono (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (payload_space t input hh taken ht) 1))
  have loop := flatIterate_uniform (stepCode t) (step t) ([0,0,0]++fields input)
    (input.period*input.height) (stepCoefficient t*(scanSpace input+1))
    (Computability.encodeNat (input.period*input.height)).length le_rfl steps
  simpa only [iterate_payload] using loop

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
