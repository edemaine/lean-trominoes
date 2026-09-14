/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBarrierSupply

/-! # The staggered lattice of I-completion bricks

Rows have height 162 and horizontal spacing 36. Successive rows are shifted
by 18. No periodicity assumption is needed for the barrier argument.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def origin (location : Cell) : Cell := (36 * location.1 + 18 * location.2,162 * location.2)

theorem origin_add (a b : Cell) : origin (Cell.add a b) = Cell.add (origin a) (origin b) := by
  apply Prod.ext <;> dsimp [origin,Cell.add] <;> omega

def globalPrescribed (palette : Cell → Fin 24) : Set (Finset Cell) :=
  {f | ∃ location : Cell, ∃ p ∈ motif (palette location),
    f = (p.shift (origin location)).cells (fun _ => Tromino.I.cells)}

def globalFilled (palette : Cell → Fin 24) : Set Cell := Tromino.occupied (globalPrescribed palette)

theorem global_prescribed_legal (palette : Cell → Fin 24) {f : Finset Cell}
    (hf : f ∈ globalPrescribed palette) : Tromino.I.IsFootprint f := by
  obtain ⟨location,p,_,rfl⟩ := hf
  exact ⟨p.shift (origin location),rfl⟩

theorem local_filled_global (palette : Cell → Fin 24) (location : Cell) {c : Cell}
    (hc : FilledAt (palette location) c) : Cell.add (origin location) c ∈ globalFilled palette := by
  obtain ⟨p,hp,hpc⟩ := (filledAt_iff _ _).mp hc
  exact ⟨_,⟨location,p,hp,rfl⟩,
    (Placement.mem_shift_cells (fun _ => Tromino.I.cells) (origin location) p c).mpr hpc⟩

end LeanTrominoes.CompletionPattern.IBricks
