/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitCompleteness

/-! # Tiling the square grid by 64-by-64 Boolean circuit macros -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

def macroOrigin (location : Cell) : Cell := (64 * location.1,64 * location.2)
def macroIndex (c : Cell) : Cell := (c.1 / 64,c.2 / 64)
def macroLocal (c : Cell) : Cell := (c.1 % 64,c.2 % 64)

theorem macro_local_inside (c : Cell) : Inside (macroLocal c) := by
  dsimp [Inside,size,macroLocal]
  omega

theorem macro_decomposition (c : Cell) : Cell.add (macroOrigin (macroIndex c)) (macroLocal c) = c := by
  apply Prod.ext <;> dsimp [Cell.add,macroOrigin,macroIndex,macroLocal] <;> omega

theorem macro_index_at (location c : Cell) (inside : Inside c) :
    macroIndex (Cell.add (macroOrigin location) c) = location := by
  apply Prod.ext <;> dsimp [Inside,size] at inside <;> dsimp [macroIndex,macroOrigin,Cell.add] <;> omega

theorem macro_local_at (location c : Cell) (inside : Inside c) :
    macroLocal (Cell.add (macroOrigin location) c) = c := by
  apply Prod.ext <;> dsimp [Inside,size] at inside <;> dsimp [macroLocal,macroOrigin,Cell.add] <;> omega

def wrappedNeighbor (c : Cell) (p : Fin 4) : Cell :=
  Cell.sub (gridNeighbor c p) (macroOrigin (gridNeighbor (0,0) p))

/-- A step out of a macro arrives at the opposite boundary of its adjacent macro. -/
theorem wrapped_boundary (c : Cell) (p : Fin 4) (inside : Inside c)
    (outside : ¬ Inside (gridNeighbor c p)) :
    Inside (wrappedNeighbor c p) ∧
      ¬ Inside (gridNeighbor (wrappedNeighbor c p) (gridOpposite p)) ∧
      (c = terminalPoint p ↔ wrappedNeighbor c p = terminalPoint (gridOpposite p)) := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    simp [Inside,size,gridNeighbor,wrappedNeighbor,macroOrigin,Cell.sub,gridOpposite,terminalPoint,Prod.ext_iff] at * <;> omega

theorem macro_boundary_neighbor (location c : Cell) (p : Fin 4) :
    gridNeighbor (Cell.add (macroOrigin location) c) p =
      Cell.add (macroOrigin (gridNeighbor location p)) (wrappedNeighbor c p) := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    apply Prod.ext <;> simp [macroOrigin,wrappedNeighbor,gridNeighbor,Cell.add,Cell.sub] <;> omega

theorem wrapped_terminal (p : Fin 4) : wrappedNeighbor (terminalPoint p) p = terminalPoint (gridOpposite p) := by
  revert p
  decide +kernel

/-- Designated terminals on adjacent macros are adjacent square-grid cells. -/
theorem macro_terminal_neighbor (location : Cell) (p : Fin 4) :
    gridNeighbor (Cell.add (macroOrigin location) (terminalPoint p)) p =
      Cell.add (macroOrigin (gridNeighbor location p)) (terminalPoint (gridOpposite p)) := by
  rw [macro_boundary_neighbor,wrapped_terminal]

end LeanTrominoes.CompletionPattern.LBricks.Circuit
