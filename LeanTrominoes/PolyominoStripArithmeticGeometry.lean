/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripArithmeticIndex
import LeanTrominoes.PolyominoStripRawTransition
import LeanTrominoes.Computability

/-! # Natural arithmetic for oriented strip placements -/

namespace LeanTrominoes.PolyominoStripWindow.Arithmetic
open Raw

def negateCode (code : Nat) : Nat :=
  if code%2 = 0 then (if code = 0 then 0 else code-1) else code+1

theorem negateCode_encode (z : Int) : negateCode (Encodable.encode z) = Encodable.encode (-z) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      change negateCode (2*(n+1)) = 2*n+1
      simp only [negateCode]
      have parity : (2*(n+1))%2 = 0 := by omega
      rw [if_pos parity,if_neg (by omega)]
      omega
  | negSucc n =>
    change negateCode (2*n+1) = 2*(n+1)
    simp only [negateCode]
    rw [if_neg (by omega)]
    omega

def bias (bound code : Nat) : Nat :=
  if code%2 = 0 then bound+code/2 else bound-(code/2+1)

theorem bias_encode (bound : Nat) (z : Int) (lo : -(bound : Int) ≤ z) :
    (bias bound (Encodable.encode z) : Int) = (bound : Int)+z := by
  cases z with
  | ofNat n =>
    change (bias bound (2*n) : Int) = (bound : Int)+(n : Int)
    simp [bias]
  | negSucc n =>
    change (bias bound (2*n+1) : Int) = (bound : Int)+Int.negSucc n
    have parity : (2*n+1)%2 ≠ 0 := by omega
    have half : (2*n+1)/2 = n := by omega
    rw [bias,if_neg parity,half]
    omega

def orientedX (symmetry x y : Nat) : Nat :=
  let base := if symmetry%2 = 0 then x else y
  if symmetry = 1 ∨ symmetry = 2 ∨ symmetry = 6 ∨ symmetry = 7 then negateCode base else base

def orientedY (symmetry x y : Nat) : Nat :=
  let base := if symmetry%2 = 0 then y else x
  if symmetry = 2 ∨ symmetry = 3 ∨ symmetry = 4 ∨ symmetry = 7 then negateCode base else base

theorem orientedX_encode (symmetry : SquareSymmetry) (c : Cell) :
    orientedX (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2) =
      Encodable.encode (symmetry.act c).1 := by
  cases symmetry <;> simp [orientedX,symmetryIndex,negateCode_encode,SquareSymmetry.act]

theorem orientedY_encode (symmetry : SquareSymmetry) (c : Cell) :
    orientedY (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2) =
      Encodable.encode (symmetry.act c).2 := by
  cases symmetry <;> simp [orientedY,symmetryIndex,negateCode_encode,SquareSymmetry.act]

/-- The biased coordinates eliminate signed arithmetic from a cell-containment check. -/
theorem inside_iff {cells : Bool → List Cell} {height bound : Nat}
    (bounded : Bounded (Raw.tiles cells) bound) (kind : Bool) (symmetry : SquareSymmetry)
    (y : Nat) (c : Cell) (hc : c ∈ cells kind) :
    (2*bound ≤ y+bias bound (orientedY (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2)) ∧
      y+bias bound (orientedY (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2)) < height+2*bound) ↔
    (0 ≤ (y : Int)-bound+(symmetry.act c).2 ∧ (y : Int)-bound+(symmetry.act c).2 < height) := by
  have coords := act_bounds bounded kind (List.mem_toFinset.mpr hc) symmetry
  rw [orientedY_encode]
  have value := bias_encode bound (symmetry.act c).2 coords.2.2.1
  omega

theorem covers_iff {cells : Bool → List Cell} {bound : Nat}
    (bounded : Bounded (Raw.tiles cells) bound) (kind : Bool) (symmetry : SquareSymmetry)
    (column y row : Nat) (c : Cell) (hc : c ∈ cells kind) :
    (column+bias bound (orientedX (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2)) = 2*bound ∧
      y+bias bound (orientedY (symmetryIndex symmetry) (Encodable.encode c.1) (Encodable.encode c.2)) = row+2*bound) ↔
    Cell.add ((column : Int),(y : Int)-bound) (symmetry.act c) = ((bound : Int),(row : Int)) := by
  have coords := act_bounds bounded kind (List.mem_toFinset.mpr hc) symmetry
  rw [orientedX_encode,orientedY_encode]
  have hx := bias_encode bound (symmetry.act c).1 coords.1
  have hy := bias_encode bound (symmetry.act c).2 coords.2.2.1
  simp only [Cell.add,Prod.mk.injEq]
  omega

end LeanTrominoes.PolyominoStripWindow.Arithmetic
