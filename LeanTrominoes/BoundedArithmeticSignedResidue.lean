/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticSignedGeometry

/-! # Comparing signed-coordinate residues with natural arithmetic -/
namespace LeanTrominoes.BoundedArithmetic.SignedGeometry
open Expr

def equalModulo (period : Expr) (a b : Signed) : Expr :=
  eqE ((a.positive+b.negative)%period) ((b.positive+a.negative)%period)

theorem equalModulo_truth (period : Expr) (a b : Signed) (values : List Nat) :
    (equalModulo period a b).Truth values ↔
      a.eval values % (period.eval values : Int) = b.eval values % (period.eval values : Int) := by
  simp only [equalModulo,truth_eq,eval_mod,eval_add]
  have cast : (a.positive.eval values+b.negative.eval values)%period.eval values =
      (b.positive.eval values+a.negative.eval values)%period.eval values ↔
      ((a.positive.eval values:Int)+b.negative.eval values)%(period.eval values:Int) =
      ((b.positive.eval values:Int)+a.negative.eval values)%(period.eval values:Int) := by
    norm_cast
  rw [cast,Int.emod_eq_emod_iff_emod_sub_eq_zero,Int.emod_eq_emod_iff_emod_sub_eq_zero]
  unfold Signed.eval
  have rearrange : (a.positive.eval values:Int)+b.negative.eval values-
      ((b.positive.eval values:Int)+a.negative.eval values) =
      ((a.positive.eval values:Int)-a.negative.eval values)-
      ((b.positive.eval values:Int)-b.negative.eval values) := by ring
  rw [rearrange]

def pointEqual (a b : Point) : Expr := andE (equal a.1 b.1) (equal a.2 b.2)
def pointEqualModulo (period : Expr) (a b : Point) : Expr :=
  andE (equalModulo period a.1 b.1) (equalModulo period a.2 b.2)

theorem pointEqual_truth (a b : Point) (values : List Nat) :
    (pointEqual a b).Truth values ↔ pointEval a values = pointEval b values := by
  simp [pointEqual,truth_and,pointEval,Prod.mk.injEq]

theorem pointEqualModulo_truth (period : Expr) (a b : Point) (values : List Nat) :
    (pointEqualModulo period a b).Truth values ↔
      ((pointEval a values).1 % (period.eval values:Int),(pointEval a values).2 % (period.eval values:Int)) =
      ((pointEval b values).1 % (period.eval values:Int),(pointEval b values).2 % (period.eval values:Int)) := by
  simp [pointEqualModulo,truth_and,equalModulo_truth,pointEval,Prod.mk.injEq]

end LeanTrominoes.BoundedArithmetic.SignedGeometry
