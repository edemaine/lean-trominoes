/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionSquareNetwork
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-! # A port-preserving diagonal refinement of the square grid

A source vertex occupies `(2*x-2*y,2*x+2*y)`. East edges follow
E,S,S,E and south edges follow S,W,W,S. The six interior route cells
and one unused cell give eight roles per source vertex. In brick
coordinates the horizontal source period becomes horizontal again.
-/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

def offset (r : Fin 8) : Cell :=
  ![(0,0),(1,0),(1,1),(1,2),(0,1),(-1,1),(-2,1),(0,2)] r

def place (c : Cell) (r : Fin 8) : Cell :=
  (2*c.1-2*c.2+(offset r).1,2*c.1+2*c.2+(offset r).2)

def roleAt (c : Cell) : Fin 8 :=
  ![![0,4,7,6],![1,2,3,5],![7,6,0,4],![3,5,1,2]]
    ⟨(c.1%4).toNat,by omega⟩ ⟨(c.2%4).toNat,by omega⟩

def sourceAt (c : Cell) : Cell :=
  ((c.1+c.2-(offset (roleAt c)).1-(offset (roleAt c)).2)/4,
    (c.2-c.1-(offset (roleAt c)).2+(offset (roleAt c)).1)/4)

theorem place_source_role (c : Cell) : place (sourceAt c) (roleAt c) = c := by
  generalize hx : c.1%4 = x
  generalize hy : c.2%4 = y
  have bx : 0 ≤ x ∧ x < 4 := by omega
  have by' : 0 ≤ y ∧ y < 4 := by omega
  obtain ⟨bx0,bx4⟩ := bx
  obtain ⟨by0,by4⟩ := by'
  interval_cases x <;> interval_cases y <;>
    apply Prod.ext <;> simp [place,sourceAt,roleAt,offset,hx,hy] <;> omega

theorem place_injective (c d : Cell) (r s : Fin 8) (h : place c r = place d s) : c = d ∧ r = s := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases r <;> fin_cases s <;>
    simp [place,offset,Prod.ext_iff,Fin.ext_iff] at hx hy ⊢ <;> omega

@[simp] theorem source_place (c : Cell) (r : Fin 8) : sourceAt (place c r) = c :=
  (place_injective _ _ _ _ (place_source_role (place c r))).1

@[simp] theorem role_place (c : Cell) (r : Fin 8) : roleAt (place c r) = r :=
  (place_injective _ _ _ _ (place_source_role (place c r))).2

theorem brick_horizontal_period (c : Cell) (r : Fin 8) (p : Int) :
    brickOfSquare (place (c.1+p,c.2) r) = Cell.add (brickOfSquare (place c r)) (2*p,0) := by
  apply Prod.ext <;> simp [brickOfSquare,place,Cell.add] <;> ring

theorem brick_row (c : Cell) (r : Fin 8) :
    (brickOfSquare (place c r)).2 = 4*c.2+(offset r).2-(offset r).1 := by
  simp [brickOfSquare,place]
  ring

theorem brick_row_bounds (c : Cell) (r : Fin 8) :
    4*c.2-1 ≤ (brickOfSquare (place c r)).2 ∧
      (brickOfSquare (place c r)).2 ≤ 4*c.2+3 := by
  rw [brick_row]
  fin_cases r <;> simp [offset] <;> omega

end LeanTrominoes.CompletionPattern.DiagonalRouting
