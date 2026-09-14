/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionILocalStates

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def OnPortal (c : Cell) : Prop := c.2 % 27 = 0 ∧ (c.1 % 18 = 5 ∨ c.1 % 18 = 14)

instance (c : Cell) : Decidable (OnPortal c) := by unfold OnPortal; infer_instance

theorem Atom.boundary_port (a : Atom) : ∀ c ∈ a.boundary, OnPortal c := by
  cases a <;> decide +kernel

theorem translated_boundary_port (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c : Cell}
    (hc : c ∈ entry.1.boundary.image (Cell.add (atomOffset location entry))) : OnPortal c := by
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
  have port := entry.1.boundary_port d hd
  have alignment := atom_micro_offset palette location he
  rw [← alignment]
  dsimp [OnPortal,Cell.add,microOrigin] at *
  omega

/-- Three consecutive cells cannot all be connector pixels. This also covers
horizontal I trominoes lying entirely on a boundary row. -/
theorem footprint_interior_cell {f : Finset Cell} (shape : Tromino.I.IsFootprint f) :
    ∃ c ∈ f, ¬ OnPortal c := by
  obtain ⟨p,rfl⟩ := shape
  by_contra absent
  push Not at absent
  have h0 := absent (Cell.add p.offset (p.symmetry.act (0,0)))
    (Finset.mem_image.mpr ⟨(0,0),by change _ ∈ Tromino.I.cells; decide,rfl⟩)
  have h1 := absent (Cell.add p.offset (p.symmetry.act (1,0)))
    (Finset.mem_image.mpr ⟨(1,0),by change _ ∈ Tromino.I.cells; decide,rfl⟩)
  have h2 := absent (Cell.add p.offset (p.symmetry.act (2,0)))
    (Finset.mem_image.mpr ⟨(2,0),by change _ ∈ Tromino.I.cells; decide,rfl⟩)
  rcases p with ⟨kind,symmetry,x,y⟩
  cases symmetry <;> dsimp [OnPortal,SquareSymmetry.act,Cell.add] at h0 h1 h2 <;> omega

/-- A legal footprint can be contained in at most one subbrick. -/
theorem tile_owner_unique (palette : Cell → Fin 24) {f : Finset Cell}
    (shape : Tromino.I.IsFootprint f) {first second : Cell} {a b : Atom × Cell}
    (ha : a ∈ layout (palette first)) (hb : b ∈ layout (palette second))
    (insideA : f ⊆ a.1.pattern.region.image (Cell.add (atomOffset first a)))
    (insideB : f ⊆ b.1.pattern.region.image (Cell.add (atomOffset second b))) :
    first = second ∧ a = b := by
  obtain ⟨c,hc,notPortal⟩ := footprint_interior_cell shape
  obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp (insideA hc)
  have notBoundary : d ∉ a.1.boundary := by
    intro member
    exact notPortal (translated_boundary_port palette first ha (Finset.mem_image.mpr ⟨d,member,eq⟩))
  apply core_region_owner palette ha hb (Finset.mem_sdiff.mpr ⟨hd,notBoundary⟩)
  rw [eq]
  exact insideB hc

/-- Every tile of any completion has exactly one subbrick owner. -/
theorem completed_tile_owner (palette : Cell → Fin 24)
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) {f : Finset Cell} (hf : f ∈ completed) :
    ∃ location : Cell, ∃ entry ∈ layout (palette location),
      f ⊆ entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  obtain ⟨c,hc,notPortal⟩ := footprint_interior_cell (h.tilesInside f hf).1
  obtain ⟨location,entry,he,inside⟩ := global_regions_cover palette c
  obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp inside
  refine ⟨location,entry,he,completed_tile_contained palette location he h retained hf (c := d) ?_ ?_⟩
  · exact Finset.mem_sdiff.mpr ⟨hd,fun member =>
      notPortal (translated_boundary_port palette location he (Finset.mem_image.mpr ⟨d,member,eq⟩))⟩
  · rwa [eq]

end LeanTrominoes.CompletionPattern.IBricks
