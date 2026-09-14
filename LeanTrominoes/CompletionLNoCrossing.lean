/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBrickLattice

/-! # Global exclusion of L-tromino crossings between subbricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem atom_barrier_global (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c : Cell}
    (hc : c ∈ entry.1.fixed ∪ entry.1.extraBarrier) :
    Cell.add (Cell.add (origin location) entry.2) c ∈ globalFilled palette := by
  have reassociate : Cell.add (Cell.add (origin location) entry.2) c =
      Cell.add (origin location) (Cell.add entry.2 c) := by
    apply Prod.ext <;> dsimp [Cell.add] <;> omega
  rw [reassociate]
  rcases Finset.mem_union.mp hc with fixed | extra
  · apply local_filled_global palette location
    refine ⟨entry,he,?_⟩
    have cancel : Cell.sub (Cell.add entry.2 c) entry.2 = c := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel]
  · exact extra_barrier_global palette location he extra

/-- Any new L tromino meeting a subbrick's interior stays in that subbrick.
The statement holds for arbitrary infinite palette assignments. -/
theorem residual_tile_contained (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {f : Finset Cell} (shape : Tromino.L.IsFootprint f)
    (avoids : ∀ d ∈ f, d ∉ globalFilled palette) {c : Cell} (hc : c ∈ entry.1.core)
    (covers : Cell.add (Cell.add (origin location) entry.2) c ∈ f) :
    f ⊆ entry.1.pattern.region.image (Cell.add (Cell.add (origin location) entry.2)) := by
  let v := Cell.add (origin location) entry.2
  let g := f.image (fun d => Cell.sub d v)
  have gshape : Tromino.L.IsFootprint g := by
    obtain ⟨p,hp⟩ := shape
    refine ⟨p.shift (Cell.sub (0,0) v),?_⟩
    dsimp [g]
    rw [← hp]
    simp only [Placement.cells,Placement.shift,Finset.image_image]
    apply Finset.image_congr
    intro d hd
    apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  have gavoids : Disjoint g (entry.1.fixed ∪ entry.1.extraBarrier) := by
    apply Finset.disjoint_left.mpr
    intro x hx hfixed
    obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp hx
    have filled := atom_barrier_global palette location he hfixed
    have cancel : Cell.add v x = y := by
      rw [← eq]
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    change Cell.add v x ∈ globalFilled palette at filled
    rw [cancel] at filled
    exact avoids y hy filled
  have gcovers : c ∈ g := by
    refine Finset.mem_image.mpr ⟨Cell.add v c,covers,?_⟩
    apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  have contained := CompletionBarrier.containment_of_avoidance entry.1.avoidance gshape gavoids gcovers hc
  intro d hd
  refine Finset.mem_image.mpr ⟨Cell.sub d v,contained (Finset.mem_image.mpr ⟨d,hd,rfl⟩),?_⟩
  apply Prod.ext <;> dsimp [v,Cell.add,Cell.sub] <;> omega

end LeanTrominoes.CompletionPattern.LBricks
