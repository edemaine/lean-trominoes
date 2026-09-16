/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripValidityExpr
import LeanTrominoes.CompletionStripOccupancy

/-! # Compiled occupancy predicate for the uncovered-cell compiler -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw
open BoundedArithmetic BoundedArithmetic.Expr

def coveredExpr (t : Tromino) (depth xfield yfield : Nat) : Expr :=
  existsE (var (depth+3)) (anyThree fun k =>
    andE (eqE (cellY t (depth+1) (var 0) (.literal k.val))
      (var (depth+1)+var (yfield+1)))
    (eqE (cellX t (depth+1) (var 0) (.literal k.val) % var (depth+3))
      ((var (depth+1)+var (xfield+1)) % var (depth+3))))

theorem coveredExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (front : List Nat) (xfield yfield x y : Nat)
    (hx : (front++fields input)[xfield]?.getD 0 = x)
    (hy : (front++fields input)[yfield]?.getD 0 = y) :
    (coveredExpr t front.length xfield yfield).Truth (front++fields input) ↔ Covered t input x y := by
  have count := header_get input front 3 (by decide)
  change (front++fields input)[front.length+3]?.getD 0 = input.motif.length at count
  simp only [coveredExpr,truth_exists,eval_var,count,anyThree_truth,truth_and,truth_eq,eval_mod,eval_add]
  have leaf (i : Nat) (hi : i < input.motif.length) (k : Fin 3) :
      ((cellY t (front.length+1) (var 0) (.literal k.val)).eval (i::(front++fields input)) =
          (i::(front++fields input))[front.length+1]?.getD 0 + (i::(front++fields input))[yfield+1]?.getD 0 ∧
        (cellX t (front.length+1) (var 0) (.literal k.val)).eval (i::(front++fields input)) %
            (i::(front++fields input))[front.length+3]?.getD 0 =
          ((i::(front++fields input))[front.length+1]?.getD 0 + (i::(front++fields input))[xfield+1]?.getD 0) %
            (i::(front++fields input))[front.length+3]?.getD 0) ↔
      ((biasedCell t (bound input) input.motif[i] k).2 = bound input+y ∧
        (biasedCell t (bound input) input.motif[i] k).1 % input.period = (bound input+x) % input.period) := by
    have cells := cellXY_eval t input (i::front) (var 0) (.literal k.val) i k hi rfl rfl
    have hb := header_get input front 0 (by decide)
    have hp := header_get input front 2 (by decide)
    simp only [List.length_cons,List.cons_append] at cells
    rw [cells.1,cells.2]
    simp only [List.getElem?_cons_succ,show front.length+3 = (front.length+2)+1 by omega]
    simp only [Nat.add_zero] at hb
    rw [hx,hy,hb,hp]
    rfl
  constructor
  · rintro ⟨i,hi,k,hk⟩
    exact ⟨input.motif[i],List.getElem_mem hi,k,(leaf i hi k).mp hk⟩
  · rintro ⟨p,hp,k,hk⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨i,hi,k,(leaf i hi k).mpr hk⟩

theorem coveredExpr_noPower (t : Tromino) (depth xfield yfield : Nat) :
    (coveredExpr t depth xfield yfield).noPower = true := by
  cases t <;> simp [coveredExpr,existsE,anyThree,cellX,cellY,fieldExpr,sourceX,sourceY,
    PolyominoStripWindow.Formula.biased,PolyominoStripWindow.Formula.orientX,
    PolyominoStripWindow.Formula.orientY,PolyominoStripWindow.Formula.negate,
    andE,orE,notE,eqE,Expr.noPower]

/-- The expression compiler's uniform bound is linear in the native field size. -/
theorem validity_code_fits (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    Turing.PartrecToTM2.EvaluatorCodeFits (validExpr t).code (fields input)
      [(validExpr t).eval (fields input)]
      (((validExpr t).weight*((validExpr t).radius+1))*(Turing.PartrecToTM2.encodedListSpace (fields input)+1)) :=
  (validExpr t).code_fits_automatic _ (validExpr_noPower t)

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw
