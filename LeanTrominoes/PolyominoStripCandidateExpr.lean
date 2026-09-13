/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripFieldExpr
import LeanTrominoes.PolyominoStripArithmeticQuantifiers

/-! # Compiled bounded quantification over strip placement records -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

/-- Bind column, kind, symmetry, and vertical position, leaving `[y,symmetry,kind,column]` in front. -/
def forallCandidates (depth : Nat) (body : Expr) : Expr :=
  .all (2*var (depth+1)+1) (.all 2 (.all 8 (.all (var (depth+3)+2*var (depth+4)+1) body)))

def existsCandidates (depth : Nat) (body : Expr) : Expr :=
  notE (forallCandidates depth (notE body))

theorem forallCandidates_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (body : Expr) :
    (forallCandidates front.length body).Truth (front ++ Arithmetic.input cells height bound first second) ↔
      ∀ a ∈ Raw.keys height bound,
        body.Truth (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) := by
  let values := front ++ Arithmetic.input cells height bound first second
  have hb := Arithmetic.header_get cells height bound first second front 1 (by decide)
  change values[front.length+1]?.getD 0 = bound at hb
  have rowCount (column kind symmetry : Nat) :
      (var (front.length+3)+2*var (front.length+4)+1).eval (symmetry :: kind :: column :: values) = height+2*bound+1 := by
    have hy := Arithmetic.header_get cells height bound first second (symmetry :: kind :: column :: front) 0 (by decide)
    have hb' := Arithmetic.header_get cells height bound first second (symmetry :: kind :: column :: front) 1 (by decide)
    change (symmetry :: kind :: column :: values)[front.length+3]?.getD 0 = height at hy
    change (symmetry :: kind :: column :: values)[front.length+4]?.getD 0 = bound at hb'
    change ((symmetry :: kind :: column :: values)[front.length+3]?.getD 0)+
      2*((symmetry :: kind :: column :: values)[front.length+4]?.getD 0)+1 = _
    rw [hy,hb']
  simp only [forallCandidates,truth_all]
  change (∀ column < 2*(values[front.length+1]?.getD 0)+1, ∀ kind < 2, ∀ symmetry < 8,
    ∀ y < (var (front.length+3)+2*var (front.length+4)+1).eval (symmetry :: kind :: column :: values),
      body.Truth (y :: symmetry :: kind :: column :: values)) ↔ _
  rw [hb]
  simp_rw [rowCount]
  exact Arithmetic.forall_candidates height bound (fun fields => body.Truth (fields ++ values))

theorem existsCandidates_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (body : Expr) :
    (existsCandidates front.length body).Truth (front ++ Arithmetic.input cells height bound first second) ↔
      ∃ a ∈ Raw.keys height bound,
        body.Truth (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) := by
  classical
  simp only [existsCandidates,truth_not,forallCandidates_truth,not_forall,_root_.not_imp,not_not,exists_prop]

theorem forallCandidates_noPower (depth : Nat) (body : Expr) (h : body.noPower = true) :
    (forallCandidates depth body).noPower = true := by
  simp [forallCandidates,Expr.noPower,h]

theorem existsCandidates_noPower (depth : Nat) (body : Expr) (h : body.noPower = true) :
    (existsCandidates depth body).noPower = true := by
  simp [existsCandidates,notE,eqE,Expr.noPower,forallCandidates_noPower, h]

end LeanTrominoes.PolyominoStripWindow.Formula
