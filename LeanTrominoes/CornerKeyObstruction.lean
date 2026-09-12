/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyTrominoObstruction
import LeanTrominoes.KeyedPeriodicComplement

/-! # Corner locks cannot be filled by the small tile -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The occupied 5-by-5 neighborhood surrounding the vertical lock. -/
def verticalPatch : Polyomino := square 5 \ verticalLock

/-- The right-hand lock, reflected into coordinates measured from the right edge. -/
def rightLock : Polyomino := {(3, 2), (3, 3), (2, 3), (1, 3), (0, 3)}

def rightPatch : Polyomino := square 5 \ rightLock

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem vertical_certificate :
    ∀ p ∈ PlusRefinement.coveringPlacements (2, 3),
      ¬ Disjoint verticalPatch (p.cells (fun _ => PlusRefinement.bumpy)) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem right_certificate :
    ∀ p ∈ PlusRefinement.coveringPlacements (3, 2),
      ¬ Disjoint rightPatch (p.cells (fun _ => PlusRefinement.bumpy)) := by decide

/-- No orientation of P can cover the bottom of the vertical lock. -/
theorem bumpy_cannot_fill_vertical_lock (p : Placement Unit)
    (covers : (2, 3) ∈ p.cells (fun _ => PlusRefinement.bumpy)) :
    ¬ Disjoint verticalPatch (p.cells (fun _ => PlusRefinement.bumpy)) :=
  vertical_certificate p ((PlusRefinement.mem_coveringPlacements _ _).mpr covers)

/-- No orientation of P can cover the hooked end of the right-hand lock. -/
theorem bumpy_cannot_fill_right_lock (p : Placement Unit)
    (covers : (3, 2) ∈ p.cells (fun _ => PlusRefinement.bumpy)) :
    ¬ Disjoint rightPatch (p.cells (fun _ => PlusRefinement.bumpy)) :=
  right_certificate p ((PlusRefinement.mem_coveringPlacements _ _).mpr covers)

end LeanTrominoes.KeyedPeriodicComplement
