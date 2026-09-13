/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCandidateExpr

/-! # Placement-bit expressions in the compiled strip transition -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

/-- The current placement occupies the four leading local fields. -/
def address (depth increment : Nat) : Expr :=
  (((var 3 + .literal increment)*2+var 2)*8+var 1)*(var depth+2*var (depth+1)+1)+var 0

def selected (depth : Nat) (next : Bool) (increment : Nat) : Expr :=
  .testBit (var (depth+(if next then 3 else 2))) (address depth increment)

theorem address_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (a : Raw.Candidate) (increment : Nat) :
    (address (front.length+4) increment).eval
      (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) =
        Raw.address height bound (a.1+increment,a.2) := by
  let values := Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)
  have len : (Arithmetic.candidateFields a ++ front).length = front.length+4 := by
    simp [Arithmetic.candidateFields]
  have hh := Arithmetic.header_get cells height bound first second (Arithmetic.candidateFields a ++ front) 0 (by decide)
  have hb := Arithmetic.header_get cells height bound first second (Arithmetic.candidateFields a ++ front) 1 (by decide)
  rw [len] at hh hb
  change values[front.length+4]?.getD 0 = height at hh
  change values[front.length+4+1]?.getD 0 = bound at hb
  change ((((values[3]?.getD 0)+increment)*2+(values[2]?.getD 0))*8+(values[1]?.getD 0))*
    ((values[front.length+4]?.getD 0)+2*(values[front.length+4+1]?.getD 0)+1)+(values[0]?.getD 0) = _
  rw [hh,hb]
  rfl

theorem selected_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (a : Raw.Candidate) (next : Bool) (increment : Nat) :
    (selected (front.length+4) next increment).Truth
      (Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second)) ↔
        (if next then second else first).testBit (Raw.address height bound (a.1+increment,a.2)) = true := by
  rw [selected,truth_bit,address_eval]
  have len : (Arithmetic.candidateFields a ++ front).length = front.length+4 := by
    simp [Arithmetic.candidateFields]
  cases next with
  | false =>
    have h := Arithmetic.header_get cells height bound first second (Arithmetic.candidateFields a ++ front) 2 (by decide)
    rw [len] at h
    change ((Arithmetic.candidateFields a ++ front) ++ Arithmetic.input cells height bound first second)[front.length+4+2]?.getD 0 = first at h
    change ((Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))[front.length+4+2]?.getD 0).testBit _ = true ↔ _
    rw [List.append_assoc] at h
    rw [h]
    simp
  | true =>
    have h := Arithmetic.header_get cells height bound first second (Arithmetic.candidateFields a ++ front) 3 (by decide)
    rw [len] at h
    change ((Arithmetic.candidateFields a ++ front) ++ Arithmetic.input cells height bound first second)[front.length+4+3]?.getD 0 = second at h
    change ((Arithmetic.candidateFields a ++ (front ++ Arithmetic.input cells height bound first second))[front.length+4+3]?.getD 0).testBit _ = true ↔ _
    rw [List.append_assoc] at h
    rw [h]
    simp

theorem address_noPower (depth increment : Nat) : (address depth increment).noPower = true := by
  simp [address,Expr.noPower]

theorem selected_noPower (depth : Nat) (next : Bool) (increment : Nat) :
    (selected depth next increment).noPower = true := by
  simp [selected,Expr.noPower,address_noPower]

end LeanTrominoes.PolyominoStripWindow.Formula
