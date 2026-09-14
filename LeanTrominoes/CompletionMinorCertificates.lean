/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionMinorWitnesses
import LeanTrominoes.CompletionMinorHoles
import LeanTrominoes.TrominoFiniteCover

/-! # Exact equal/not relations for the finite completion gadgets -/

namespace LeanTrominoes.CompletionMinor

def residualCells (t : Tromino) (gate : Gate) (a b : Bool) : List Cell :=
  (holes t gate).filter (fun c => c ∉ externalPorts t a b)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem residual_cells (t : Tromino) (gate : Gate) (a b : Bool) :
    (residualCells t gate a b).toFinset = target t gate a b \
      (prefill t gate).biUnion (Placement.cells (fun _ => t.cells)) := by
  cases t <;> cases gate <;> cases a <;> cases b <;> decide +kernel

theorem residual_tileable_of_completable (t : Tromino) (gate : Gate) (a b : Bool)
    (h : t.Completable (target t gate a b : Set Cell)
      (t.finiteFootprints (prefill t gate) : Set (Finset Cell))) :
    t.Tileable ((residualCells t gate a b).toFinset : Set Cell) := by
  have tiled := ((t.completable_iff _ _).mp h).2
  have eq : (target t gate a b : Set Cell) \
      Tromino.occupied (t.finiteFootprints (prefill t gate) : Set (Finset Cell)) =
      ((residualCells t gate a b).toFinset : Set Cell) := by
    rw [residual_cells]
    ext c
    simp [Tromino.occupied,Tromino.finiteFootprints]
  rwa [eq] at tiled

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem wrong_state_search_empty (t : Tromino) (gate : Gate) (value : Bool) :
    TrominoFiniteCover.search t (residualCells t gate value (!(output gate value))) = [] := by
  cases t <;> cases gate <;> cases value <;> decide +kernel

end LeanTrominoes.CompletionMinor
