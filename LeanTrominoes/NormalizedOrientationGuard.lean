/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationGuardExpressions

/-! # Complete native drawing validity guard for normalized orientation -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.Guard
open PeriodicOrthogonalDrawing FlatEncoding BoundedArithmetic BoundedArithmetic.Expr FieldQueries GuardExpressions

def checks : Expr := .all (var 1) (.all (var 3) localChecks)

theorem checks_truth (d : PeriodicOrthogonalDrawing) : checks.Truth (context d) ↔ ∀ p : d.Position, ∀ side,
    (d.get p).portColor side = (d.get (d.neighbor p side)).portColor side.opposite ∧
    ((d.get p).isVertex = true → (d.get (d.neighbor p side)).isVertex = false) := by
  simp only [checks,truth_all]
  change (∀ x < d.horizontalPeriod, ∀ y < d.verticalPeriod, localChecks.Truth (y::x::context d)) ↔ _
  constructor
  · intro h p
    exact (localChecks_truth d p).mp (h p.1.val p.1.isLt p.2.val p.2.isLt)
  · intro h x hx y hy
    exact (localChecks_truth d (⟨x,hx⟩,⟨y,hy⟩)).mpr (h _)

-- Boundary context: x, field count, width, height, cell codes.
def firstRow : Expr := cell 2 (var 0)
def lastRow : Expr := cell 2 ((var 3-1)*var 2+var 0)
def blankRows : Expr := .all (var 1) (andE (eqE firstRow 0) (eqE lastRow 0))

theorem firstRow_eval (d : PeriodicOrthogonalDrawing) (x : Fin (d.horizontalPeriodPred+1)) :
    firstRow.eval (x.val::context d) = cellCode (d.get (x,0)) := by
  have h := cell_eval d [x.val,(fields d).length] (var 0)
  change firstRow.eval (x.val::context d) = cellCode (d.cellTypes.getD x.val .blank) at h
  simpa only [PeriodicOrthogonalDrawing.get,Fin.val_zero,Nat.zero_mul,Nat.zero_add] using h

theorem lastRow_eval (d : PeriodicOrthogonalDrawing) (x : Fin (d.horizontalPeriodPred+1)) :
    lastRow.eval (x.val::context d) = cellCode (d.get (x,Fin.last d.verticalPeriodPred)) := by
  have h := cell_eval d [x.val,(fields d).length] ((var 3-1)*var 2+var 0)
  exact h

private theorem blank_iff (c : OrthogonalCellType) : cellCode c = 0 ↔ c = .blank := by
  rw [← cellCode_blank,cellCode_injective.eq_iff]

theorem blankRows_truth (d : PeriodicOrthogonalDrawing) : blankRows.Truth (context d) ↔ d.HasBlankVerticalBoundary := by
  rw [blankVerticalBoundary_iff_rows]
  simp only [blankRows,truth_all,truth_and,truth_eq]
  change (∀ x < d.horizontalPeriod, firstRow.eval (x::context d) = 0 ∧ lastRow.eval (x::context d) = 0) ↔ _
  constructor
  · intro h x
    have hx := h x.val x.isLt
    simpa only [firstRow_eval,lastRow_eval,blank_iff] using hx
  · intro h x hx
    have hrow := h ⟨x,hx⟩
    rw [firstRow_eval d ⟨x,hx⟩,lastRow_eval d ⟨x,hx⟩,blank_iff,blank_iff]
    exact hrow

def lengthMatch : Expr := eqE (var 0) (var 1*var 2+2)
def guard : Expr := andE lengthMatch (andE checks blankRows)

def Metadata (d : PeriodicOrthogonalDrawing) : Prop :=
  d.IsWellFormed ∧ d.VerticesSeparated ∧ d.HasBlankVerticalBoundary

theorem lengthMatch_truth (d : PeriodicOrthogonalDrawing) :
    lengthMatch.Truth (context d) ↔ d.cellTypes.length = d.horizontalPeriod*d.verticalPeriod := by
  rw [lengthMatch,truth_eq]
  change (fields d).length = d.horizontalPeriod*d.verticalPeriod+2 ↔ _
  simp only [fields,List.length_cons,List.length_map]
  omega

theorem guard_truth (d : PeriodicOrthogonalDrawing) : guard.Truth (context d) ↔ Metadata d := by
  rw [guard,truth_and,truth_and,lengthMatch_truth,checks_truth,blankRows_truth]
  simp only [forall_and,Metadata,PeriodicOrthogonalDrawing.IsWellFormed,VerticesSeparated,horizontalPeriod,verticalPeriod]
  tauto

theorem guard_noPower : guard.noPower = true := by
  simp [guard,lengthMatch,checks,blankRows,firstRow,lastRow,cell,andE,eqE,Expr.noPower,var,localChecks_noPower]

def decision : Expr := .ite guard 1 0

def result (d : PeriodicOrthogonalDrawing) : Bool := decide (guard.eval (context d) ≠ 0)

theorem result_correct (d : PeriodicOrthogonalDrawing) : result d = true ↔ Metadata d := by
  simp only [result,decide_eq_true_eq]
  exact guard_truth d

theorem decision_eval (d : PeriodicOrthogonalDrawing) : decision.eval (context d) = (result d).toNat := by
  by_cases h : guard.eval (context d) = 0 <;> simp [decision,Expr.eval,result,h]

theorem decision_noPower : decision.noPower = true := by simp [decision,Expr.noPower,guard_noPower]

end LeanTrominoes.Gadget.NormalizedOrientation.Guard
end
