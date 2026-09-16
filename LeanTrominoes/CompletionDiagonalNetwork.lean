/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalRouting

/-! # Boolean networks on the diagonal routing refinement -/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

/-- Copy labels for route interiors; the last role is unused. -/
def wireLabel (r : Fin 8) : Fin 24 := ![0,3,9,12,10,6,5,0] r

def refinePalette (palette : Cell → Fin 24) (c : Cell) : Fin 24 :=
  if roleAt c = 0 then palette (sourceAt c) else wireLabel (roleAt c)

def liftAt (v : Cell → Fin 4 → Bool) (c : Cell) (r : Fin 8) (p : Fin 4) : Bool :=
  if r = 0 then v c p else
    if active (wireLabel r) p then (if r.val < 4 then v c 1 else v c 3) else false

def liftValue (v : Cell → Fin 4 → Bool) (c : Cell) : Fin 4 → Bool :=
  liftAt v (sourceAt c) (roleAt c)

@[simp] theorem palette_place (palette : Cell → Fin 24) (c : Cell) (r : Fin 8) :
    refinePalette palette (place c r) = if r = 0 then palette c else wireLabel r := by
  simp [refinePalette]

@[simp] theorem lift_place (v : Cell → Fin 4 → Bool) (c : Cell) (r : Fin 8) :
    liftValue v (place c r) = liftAt v c r := by simp [liftValue]

def neighborOffset (r : Fin 8) (p : Fin 4) : Cell :=
  ![![(0,-1),(0,0),(-1,0),(0,0)],
    ![(0,-1),(0,-1),(0,0),(0,0)],
    ![(0,0),(1,-1),(0,0),(0,0)],
    ![(0,0),(1,0),(0,0),(1,0)],
    ![(0,0),(0,0),(0,0),(0,0)],
    ![(-1,0),(0,0),(0,0),(0,1)],
    ![(-1,0),(0,0),(-1,1),(0,1)],
    ![(0,0),(0,0),(0,1),(1,0)]] r p

def neighborRole (r : Fin 8) (p : Fin 4) : Fin 8 :=
  ![![6,1,3,4],![5,7,0,2],![1,6,4,3],![2,0,7,5],
    ![0,2,5,7],![3,4,6,1],![7,5,2,0],![4,3,1,6]] r p

theorem neighbor_place (c : Cell) (r : Fin 8) (p : Fin 4) :
    gridNeighbor (place c r) p = place (Cell.add c (neighborOffset r p)) (neighborRole r p) := by
  fin_cases r <;> fin_cases p <;> apply Prod.ext <;>
    simp [gridNeighbor,place,offset,neighborOffset,neighborRole,Cell.add] <;> ring

theorem lift_seams (v : Cell → Fin 4 → Bool) (hv : SquareSeams v) : SquareSeams (liftValue v) := by
  intro location p
  obtain ⟨c,r,eq⟩ : ∃ c r, place c r = location := ⟨sourceAt location,roleAt location,place_source_role location⟩
  rw [← eq,neighbor_place,lift_place,lift_place]
  have h0 := hv c 0
  have h1 := hv c 1
  have h2 := hv c 2
  have h3 := hv c 3
  simp only [gridNeighbor,gridOpposite] at h0 h1 h2 h3
  fin_cases r <;> fin_cases p <;>
    simp [liftAt,neighborOffset,neighborRole,wireLabel,active,bit,gridOpposite,Cell.add] <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h0.symm | exact h1.symm | exact h2.symm | exact h3.symm

theorem wire_lift_valid (v : Cell → Fin 4 → Bool) (c : Cell) (r : Fin 8) (hr : r ≠ 0) :
    Network (wireLabel r) (liftAt v c r) := by
  have bound : (wireLabel r).val < 16 := by fin_cases r <;> decide
  rw [network_iff,if_pos bound]
  refine ⟨?_,if r.val < 4 then v c 1 else v c 3,?_⟩
  · intro p hp
    simp [liftAt,hr,hp]
  · intro p hp
    simp [liftAt,hr,hp]

end LeanTrominoes.CompletionPattern.DiagonalRouting
