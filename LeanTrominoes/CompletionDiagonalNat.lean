/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalPeriod

/-! # Natural-coordinate decoding of the diagonal brick layout -/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

def natRole (x y : Nat) : Fin 8 :=
  if x%2 = 0 then ![0,4,7,6] ⟨y%4,by omega⟩
  else ![2,3,5,1] ⟨y%4,by omega⟩
def natSourceX (x y : Nat) : Nat :=
  x/2+y/4 + if y%4 = 3 ∨ (y%4 = 2 ∧ x%2 = 1) then 1 else 0
def natSourceY (x y : Nat) : Nat :=
  y/4 + if y%4 = 3 ∧ x%2 = 1 then 1 else 0

theorem nat_decode (x y : Nat) :
    brickOfSquare (place (natSourceX x y,natSourceY x y) (natRole x y)) = ((x:Int),(y:Int)) := by
  generalize hx : x%2 = a
  generalize hy : y%4 = b
  have ha : a < 2 := by omega
  have hb : b < 4 := by omega
  interval_cases a <;> interval_cases b <;>
    apply Prod.ext <;>
    simp [brickOfSquare,place,offset,natSourceX,natSourceY,natRole,hx,hy] <;> omega

theorem sourceAt_nat (x y : Nat) :
    sourceAt (squareOfBrick ((x:Int),(y:Int))) = ((natSourceX x y : Int),(natSourceY x y : Int)) := by
  rw [← nat_decode x y,square_of_brick_of_square,source_place]

theorem roleAt_nat (x y : Nat) :
    roleAt (squareOfBrick ((x:Int),(y:Int))) = natRole x y := by
  rw [← nat_decode x y,square_of_brick_of_square,role_place]
end LeanTrominoes.CompletionPattern.DiagonalRouting
