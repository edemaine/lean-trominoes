/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionICoreSeparation

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

theorem Atom.fixed_inside (a : Atom) : a.fixed ⊆ a.pattern.region := by
  cases a <;> simp only [Finset.subset_iff,Atom.mem_region] <;> decide +kernel

theorem Atom.motif_inside (a : Atom) {p : Placement Unit} (hp : p ∈ a.motif) :
    p.cells (fun _ => Tromino.I.cells) ⊆ a.pattern.region := by
  intro c hc
  exact a.fixed_inside ((a.fixed_mem c).mpr ⟨p,hp,hc⟩)

theorem shift_cells_twice (p : Placement Unit) (u v : Cell) :
    ((p.shift v).shift u).cells (fun _ => Tromino.I.cells) =
      (p.shift (Cell.add u v)).cells (fun _ => Tromino.I.cells) := by
  simp only [Placement.cells,Placement.shift]
  apply Finset.image_congr
  intro c hc
  apply Prod.ext <;> dsimp [Cell.add] <;> omega

theorem shifted_motif_inside (location : Cell) (entry : Atom × Cell)
    {p : Placement Unit} (hp : p ∈ entry.1.motif) :
    (p.shift (atomOffset location entry)).cells (fun _ => Tromino.I.cells) ⊆
      entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  intro c hc
  let d := Cell.sub c (atomOffset location entry)
  have cancel : Cell.add (atomOffset location entry) d = c := by
    apply Prod.ext <;> dsimp [d,Cell.add,Cell.sub] <;> omega
  have hd : d ∈ p.cells (fun _ => Tromino.I.cells) := by
    apply (Placement.mem_shift_cells _ _ p d).mp
    rwa [cancel]
  exact Finset.mem_image.mpr ⟨d,entry.1.motif_inside hp hd,cancel⟩

theorem prescribed_atom (palette : Cell → Fin 24) {f : Finset Cell}
    (hf : f ∈ globalPrescribed palette) :
    ∃ location : Cell, ∃ entry ∈ layout (palette location), ∃ p ∈ entry.1.motif,
      f = (p.shift (atomOffset location entry)).cells (fun _ => Tromino.I.cells) := by
  obtain ⟨location,q,hq,rfl⟩ := hf
  obtain ⟨entry,he,hq⟩ := List.mem_flatMap.mp hq
  change q ∈ entry.1.motif.map (fun p => p.shift entry.2) at hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact ⟨location,entry,he,p,hp,shift_cells_twice p _ _⟩

theorem atom_prescribed (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {p : Placement Unit} (hp : p ∈ entry.1.motif) :
    (p.shift (atomOffset location entry)).cells (fun _ => Tromino.I.cells) ∈
      globalPrescribed palette := by
  refine ⟨location,p.shift entry.2,List.mem_flatMap.mpr
    ⟨entry,he,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,?_⟩
  exact (shift_cells_twice p _ _).symm

/-- A preplaced tile meeting a subbrick interior is one of its own preplacements. -/
theorem prescribed_core_owner (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {f : Finset Cell} (hf : f ∈ globalPrescribed palette) {c : Cell}
    (hc : c ∈ entry.1.pattern.region \ entry.1.boundary)
    (covers : Cell.add (atomOffset location entry) c ∈ f) :
    ∃ p ∈ entry.1.motif,
      f = (p.shift (atomOffset location entry)).cells (fun _ => Tromino.I.cells) := by
  obtain ⟨other,b,hb,p,hp,eq⟩ := prescribed_atom palette hf
  have inside := shifted_motif_inside other b hp
  rw [← eq] at inside
  obtain ⟨rfl,rfl⟩ := core_region_owner palette he hb hc (inside covers)
  exact ⟨p,hp,eq⟩

end LeanTrominoes.CompletionPattern.IBricks
