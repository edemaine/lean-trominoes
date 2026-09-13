/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.PartrecLinearAdaptersSpace

/-! # Fixed literal headers with linear evaluator workspace -/

namespace Turing.ToPartrec.Code

def prefixLiterals : List Nat → Code → Code
  | [],rest => rest
  | value :: values,rest => prepend (numeral value) (prefixLiterals values rest)

theorem prefixLiterals_eval (front : List Nat) (rest : Code) (values output : List Nat)
    (run : rest.eval values = pure output) :
    (prefixLiterals front rest).eval values = pure (front ++ output) := by
  induction front with
  | nil => exact run
  | cons value front ih => simp [prefixLiterals,ih]

end Turing.ToPartrec.Code

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec LeanTrominoes.BoundedArithmetic

def literalCoefficient (value : Nat) : Nat := (Expr.literal value).weight*((Expr.literal value).radius+1)

def prefixCoefficient : List Nat → Nat → Nat
  | [],rest => rest
  | value :: values,rest => 4*(literalCoefficient value+prefixCoefficient values rest+1)

theorem literal_linear (value : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.numeral value) values [value] (literalCoefficient value*(encodedListSpace values+1)) :=
  (Expr.literal value).code_fits_automatic values rfl

theorem prefixLiterals_linear (front : List Nat) {rest : Code} {values output : List Nat} {coefficient : Nat}
    (fit : EvaluatorCodeFits rest values output (coefficient*(encodedListSpace values+1))) :
    EvaluatorCodeFits (Code.prefixLiterals front rest) values (front ++ output)
      (prefixCoefficient front coefficient*(encodedListSpace values+1)) := by
  induction front with
  | nil => exact fit
  | cons value front ih => exact prepend_linear (literal_linear value values) ih

end Turing.PartrecToTM2.EvaluatorCodeFits
