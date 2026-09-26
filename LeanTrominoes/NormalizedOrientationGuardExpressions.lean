/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationFiniteCoordinates
import LeanTrominoes.NormalizedOrientationFieldQueries

/-! # Native arithmetic expressions for orientation drawing validity -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.GuardExpressions
open PeriodicOrthogonalDrawing FlatEncoding BoundedArithmetic BoundedArithmetic.Expr FieldQueries

def context (d : PeriodicOrthogonalDrawing) : List Nat := (fields d).length :: fields d

-- Local context: y, x, field count, width, height, cell codes.
def current : Expr := cell 3 (var 0*var 3+var 1)
def neighborIndex : Side → Expr
  | .north => ((var 0+var 4-1)%var 4)*var 3+var 1
  | .east => var 0*var 3+(var 1+1)%var 3
  | .south => ((var 0+1)%var 4)*var 3+var 1
  | .west => var 0*var 3+(var 1+var 3-1)%var 3

def next (side : Side) : Expr := cell 3 (neighborIndex side)

theorem current_eval (d : PeriodicOrthogonalDrawing) (p : d.Position) :
    current.eval (p.2.val::p.1.val::context d) = cellCode (d.get p) :=
  cell_eval d [p.2.val,p.1.val,(fields d).length] (var 0*var 3+var 1)

theorem neighborIndex_eval (d : PeriodicOrthogonalDrawing) (x y : Nat) (side : Side) :
    (neighborIndex side).eval (y::x::context d) =
      (neighborCoordinates d.horizontalPeriod d.verticalPeriod x y side).2*d.horizontalPeriod +
      (neighborCoordinates d.horizontalPeriod d.verticalPeriod x y side).1 := by
  cases side <;> rfl

theorem next_eval (d : PeriodicOrthogonalDrawing) (p : d.Position) (side : Side) :
    (next side).eval (p.2.val::p.1.val::context d) = cellCode (d.get (d.neighbor p side)) := by
  have h := cell_eval d [p.2.val,p.1.val,(fields d).length] (neighborIndex side)
  change (next side).eval (p.2.val::p.1.val::context d) =
    cellCode (d.cellTypes.getD ((neighborIndex side).eval (p.2.val::p.1.val::context d)) .blank) at h
  rw [neighborIndex_eval] at h
  have equal := congrArg (fun q : Nat × Nat => d.cellTypes.getD (q.2*d.horizontalPeriod+q.1) .blank)
    (neighbor_values d p side)
  exact h.trans (congrArg cellCode equal.symm)

def sideCheck (side : Side) : Expr :=
  andE (eqE (port side current) (port side.opposite (next side)))
    (impE (vertex current) (notE (vertex (next side))))

theorem sideCheck_truth (d : PeriodicOrthogonalDrawing) (p : d.Position) (side : Side) :
    (sideCheck side).Truth (p.2.val::p.1.val::context d) ↔
      (d.get p).portColor side = (d.get (d.neighbor p side)).portColor side.opposite ∧
      ((d.get p).isVertex = true → (d.get (d.neighbor p side)).isVertex = false) := by
  rw [sideCheck,truth_and,truth_eq,truth_imp,truth_not]
  rw [port_eval side current _ _ (current_eval d p),
    port_eval side.opposite (next side) _ _ (next_eval d p side),Encodable.encode_inj]
  simp only [Truth,vertex_eval current _ _ (current_eval d p),
    vertex_eval (next side) _ _ (next_eval d p side)]
  cases (d.get p).isVertex <;> cases (d.get (d.neighbor p side)).isVertex <;> simp

def localChecks : Expr := andE (sideCheck .north)
  (andE (sideCheck .east) (andE (sideCheck .south) (sideCheck .west)))

theorem localChecks_truth (d : PeriodicOrthogonalDrawing) (p : d.Position) :
    localChecks.Truth (p.2.val::p.1.val::context d) ↔ ∀ side,
      (d.get p).portColor side = (d.get (d.neighbor p side)).portColor side.opposite ∧
      ((d.get p).isVertex = true → (d.get (d.neighbor p side)).isVertex = false) := by
  simp only [localChecks,truth_and,sideCheck_truth]
  constructor
  · rintro ⟨hn,he,hs,hw⟩ side
    cases side <;> assumption
  · intro h
    exact ⟨h .north,h .east,h .south,h .west⟩

theorem sideCheck_noPower (side : Side) : (sideCheck side).noPower = true := by
  have hc : current.noPower = true := cell_noPower _ _ rfl
  have hn : (next side).noPower = true := cell_noPower _ _ (by cases side <;> rfl)
  simp only [sideCheck,andE,impE,notE,eqE,Expr.noPower,port_noPower _ _ hc,
    port_noPower _ _ hn,vertex_noPower _ hc,vertex_noPower _ hn,Bool.true_and]

theorem localChecks_noPower : localChecks.noPower = true := by
  simp [localChecks,andE,Expr.noPower,sideCheck_noPower]

end LeanTrominoes.Gadget.NormalizedOrientation.GuardExpressions
end
