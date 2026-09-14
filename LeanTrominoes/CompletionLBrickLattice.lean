/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBarrierSupply

/-! # The staggered lattice of L-completion bricks

Rows have height 36 and horizontal spacing 24. Successive rows are shifted
by 12. No periodicity assumption is needed for the barrier argument.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def origin (location : Cell) : Cell := (24 * location.1 + 12 * location.2,36 * location.2)

theorem origin_add (a b : Cell) : origin (Cell.add a b) = Cell.add (origin a) (origin b) := by
  apply Prod.ext <;> dsimp [origin,Cell.add] <;> omega

def globalPrescribed (palette : Cell → Fin 24) : Set (Finset Cell) :=
  {f | ∃ location : Cell, ∃ p ∈ motif (palette location),
    f = (p.shift (origin location)).cells (fun _ => Tromino.L.cells)}

def globalFilled (palette : Cell → Fin 24) : Set Cell := Tromino.occupied (globalPrescribed palette)

theorem global_prescribed_legal (palette : Cell → Fin 24) {f : Finset Cell}
    (hf : f ∈ globalPrescribed palette) : Tromino.L.IsFootprint f := by
  obtain ⟨location,p,_,rfl⟩ := hf
  exact ⟨p.shift (origin location),rfl⟩

theorem local_filled_global (palette : Cell → Fin 24) (location : Cell) {c : Cell}
    (hc : FilledAt (palette location) c) : Cell.add (origin location) c ∈ globalFilled palette := by
  obtain ⟨p,hp,hpc⟩ := (filledAt_iff _ _).mp hc
  exact ⟨_,⟨location,p,hp,rfl⟩,
    (Placement.mem_shift_cells (fun _ => Tromino.L.cells) (origin location) p c).mpr hpc⟩

theorem neighboring_skin_filled (palette : Cell → Fin 24) (location neighbor : Cell)
    (skin : Finset Cell) (supplied : ∀ i : Fin 24, ∀ c ∈ skin, FilledAt i c) :
    ∀ c ∈ skin.image (Cell.add (origin neighbor)),
      Cell.add (origin location) c ∈ globalFilled palette := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
  have filled := local_filled_global palette (Cell.add location neighbor)
    (supplied (palette (Cell.add location neighbor)) d hd)
  have eq : Cell.add (origin (Cell.add location neighbor)) d =
      Cell.add (origin location) (Cell.add (origin neighbor) d) := by
    rw [origin_add]
    apply Prod.ext <;> dsimp [Cell.add] <;> omega
  rwa [eq] at filled

/-- Neighboring prefills supply every external barrier cell. -/
theorem external_skin_global (palette : Cell → Fin 24) (location : Cell) {c : Cell}
    (hc : c ∈ externalSkin) : Cell.add (origin location) c ∈ globalFilled palette := by
  have covered := external_skin_covered hc
  simp only [Finset.mem_union] at covered
  rcases covered with ((aboveLeft | aboveRight) | belowLeft) | belowRight
  · have supplied := neighboring_skin_filled palette location (0,-1) bottomSkin bottom_skin_filled
    have eq : origin (0,-1) = (-12,-36) := by decide
    rw [eq] at supplied
    exact supplied c aboveLeft
  · have supplied := neighboring_skin_filled palette location (1,-1) bottomSkin bottom_skin_filled
    have eq : origin (1,-1) = (12,-36) := by decide
    rw [eq] at supplied
    exact supplied c aboveRight
  · have supplied := neighboring_skin_filled palette location (-1,1) topSkin top_skin_filled
    have eq : origin (-1,1) = (-12,36) := by decide
    rw [eq] at supplied
    exact supplied c belowLeft
  · have supplied := neighboring_skin_filled palette location (0,1) topSkin top_skin_filled
    have eq : origin (0,1) = (12,36) := by decide
    rw [eq] at supplied
    exact supplied c belowRight

/-- All six atom barrier certificates apply in every brick of an arbitrary
palette assignment on the infinite staggered lattice. -/
theorem extra_barrier_global (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c : Cell}
    (hc : c ∈ entry.1.extraBarrier) :
    Cell.add (origin location) (Cell.add entry.2 c) ∈ globalFilled palette := by
  rcases extra_supplied (palette location) entry he c hc with own | neighbor
  · exact local_filled_global palette location own
  · exact external_skin_global palette location neighbor

end LeanTrominoes.CompletionPattern.LBricks
