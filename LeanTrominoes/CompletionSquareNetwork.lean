/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBrickEquivalence

/-! # Square-grid coordinates for the Boolean brick network

Port order is north, east, west, south, matching the brick's top-left,
top-right, bottom-left, bottom-right connector order.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def gridOpposite (p : Fin 4) : Fin 4 := ⟨3 - p.val,by omega⟩

def gridNeighbor (c : Cell) (p : Fin 4) : Cell :=
  match p.val with
  | 0 => (c.1,c.2 - 1)
  | 1 => (c.1 + 1,c.2)
  | 2 => (c.1 - 1,c.2)
  | _ => (c.1,c.2 + 1)

def brickNeighbor (c : Cell) (p : Fin 4) : Cell :=
  match p.val with
  | 0 => (c.1,c.2 - 1)
  | 1 => (c.1 + 1,c.2 - 1)
  | 2 => (c.1 - 1,c.2 + 1)
  | _ => (c.1,c.2 + 1)

def brickOfSquare (c : Cell) : Cell := (c.1,c.2 - c.1)
def squareOfBrick (c : Cell) : Cell := (c.1,c.2 + c.1)

@[simp] theorem square_of_brick_of_square (c : Cell) : squareOfBrick (brickOfSquare c) = c := by
  apply Prod.ext <;> dsimp [squareOfBrick,brickOfSquare] <;> omega

@[simp] theorem brick_of_square_of_brick (c : Cell) : brickOfSquare (squareOfBrick c) = c := by
  apply Prod.ext <;> dsimp [squareOfBrick,brickOfSquare] <;> omega

theorem four_ports (p : Fin 4) : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega

theorem brick_of_square_neighbor (c : Cell) (p : Fin 4) :
    brickOfSquare (gridNeighbor c p) = brickNeighbor (brickOfSquare c) p := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    apply Prod.ext <;> simp [gridNeighbor,brickNeighbor,brickOfSquare] <;> omega

theorem square_of_brick_neighbor (c : Cell) (p : Fin 4) :
    squareOfBrick (brickNeighbor c p) = gridNeighbor (squareOfBrick c) p := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    apply Prod.ext <;> simp [gridNeighbor,brickNeighbor,squareOfBrick] <;> omega

def SquareSeams (external : Cell → Fin 4 → Bool) : Prop :=
  ∀ c p, external c p = external (gridNeighbor c p) (gridOpposite p)

def AllBrickSeams (external : Cell → Fin 4 → Bool) : Prop :=
  ∀ c p, external c p = external (brickNeighbor c p) (gridOpposite p)

theorem external_seams_iff_all (external : Cell → Fin 4 → Bool) :
    ExternalSeams external ↔ AllBrickSeams external := by
  constructor
  · intro h c p
    rcases four_ports p with rfl | rfl | rfl | rfl
    · have supplied := h (brickNeighbor c 0) 1
      simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using supplied.symm
    · have supplied := h (brickNeighbor c 1) 0
      simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using supplied.symm
    · have supplied := h c 0
      simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using supplied
    · have supplied := h c 1
      simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using supplied
  · intro h c x
    have cases : x = 0 ∨ x = 1 := by omega
    rcases cases with rfl | rfl
    · simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using h c 2
    · simpa [brickNeighbor,gridOpposite,belowBrick,oppositeColumn,Cell.add,sub_eq_add_neg] using h c 3

theorem square_seams_to_bricks (external : Cell → Fin 4 → Bool) :
    SquareSeams external ↔ ExternalSeams (fun c => external (squareOfBrick c)) := by
  rw [external_seams_iff_all]
  constructor
  · intro h c p
    change external (squareOfBrick c) p = external (squareOfBrick (brickNeighbor c p)) (gridOpposite p)
    rw [square_of_brick_neighbor]
    exact h _ _
  · intro h c p
    have supplied := h (brickOfSquare c) p
    simpa only [square_of_brick_of_square,square_of_brick_neighbor] using supplied

def SquareNetwork (palette : Cell → Fin 24) (external : Cell → Fin 4 → Bool) : Prop :=
  SquareSeams external ∧ ∀ c, Network (palette c) (external c)

def SquareHolds (palette : Cell → Fin 24) : Prop := ∃ external, SquareNetwork palette external

/-- Relabeling the square grid as a staggered brick lattice preserves all
local constraints and neighbor equations. -/
theorem square_holds_iff_completion (palette : Cell → Fin 24) :
    SquareHolds palette ↔
      Tromino.L.Completable Set.univ (globalPrescribed (fun c => palette (squareOfBrick c))) := by
  rw [completion_iff_brick_network]
  constructor
  · rintro ⟨external,seams,valid⟩
    exact ⟨fun c => external (squareOfBrick c),(square_seams_to_bricks external).mp seams,
      fun c => valid (squareOfBrick c)⟩
  · rintro ⟨external,seams,valid⟩
    refine ⟨fun c => external (brickOfSquare c),?_,?_⟩
    · apply (square_seams_to_bricks _).mpr
      simpa only [brick_of_square_of_brick] using seams
    · intro c
      simpa only [square_of_brick_of_square] using valid (brickOfSquare c)

end LeanTrominoes.CompletionPattern.LBricks
