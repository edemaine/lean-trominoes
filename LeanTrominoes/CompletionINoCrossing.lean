/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIPrefillGeometry
import LeanTrominoes.CompletionConflictBarrierTranslation

/-! # Global exclusion of I-tromino crossings between subbricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem atom_barrier_global (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c : Cell}
    (hc : c ∈ entry.1.fixed) :
    Cell.add (Cell.add (origin location) entry.2) c ∈ globalFilled palette := by
  have reassociate : Cell.add (Cell.add (origin location) entry.2) c =
      Cell.add (origin location) (Cell.add entry.2 c) := by
    apply Prod.ext <;> dsimp [Cell.add] <;> omega
  rw [reassociate]
  apply local_filled_global palette location
  refine ⟨entry,he,?_⟩
  have cancel : Cell.sub (Cell.add entry.2 c) entry.2 = c := by
    apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  rwa [cancel]

theorem atom_available_unfilled (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {c : Cell}
    (hc : c ∈ entry.1.available) : Cell.add (atomOffset location entry) c ∉ globalFilled palette := by
  have core := Finset.mem_sdiff.mp (entry.1.available_core hc)
  have inner := Finset.mem_sdiff.mp core.1
  rintro ⟨g,hg,hgc⟩
  obtain ⟨p,hp,eq⟩ := prescribed_core_owner palette location he hg
    (Finset.mem_sdiff.mpr ⟨inner.1,core.2⟩) hgc
  rw [eq] at hgc
  have localCover := (Placement.mem_shift_cells (fun _ => Tromino.I.cells) (atomOffset location entry) p c).mp hgc
  exact inner.2 ((entry.1.fixed_mem c).mpr ⟨p,hp,localCover⟩)

theorem disjoint_atom_barrier (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location)) {f : Finset Cell}
    (avoids : ∀ d ∈ f, d ∉ globalFilled palette) :
    Disjoint f (entry.1.fixed.image (Cell.add (atomOffset location entry))) := by
  apply Finset.disjoint_left.mpr
  intro d hd member
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp member
  exact avoids _ hd (atom_barrier_global palette location he hc)

/-- No new I tromino crosses a guarded subbrick boundary. The additional
conflict check rules out a straight tromino centered on a connector. -/
theorem residual_tile_contained (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) {f : Finset Cell} (hf : f ∈ completed)
    (avoids : ∀ d ∈ f, d ∉ globalFilled palette) {c : Cell} (hc : c ∈ entry.1.core)
    (covers : Cell.add (atomOffset location entry) c ∈ f) :
    f ⊆ entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  apply CompletionBarrier.containment_of_guarded_at h (atomOffset location entry)
    (fun _ _ => trivial) ?_ entry.1.guarded hf (disjoint_atom_barrier palette location he avoids) covers hc
  intro g hg d hd hgd
  have absent : g ∉ globalPrescribed palette := by
    intro prescribed
    exact atom_available_unfilled palette location he hd ⟨g,prescribed,hgd⟩
  apply disjoint_atom_barrier palette location he
  intro e hge filled
  obtain ⟨q,hq,hqe⟩ := filled
  have eq := (h.partial (Set.Subset.refl completed)).nonoverlap g hg q (retained hq) e hge hqe
  exact absent (eq ▸ hq)

end LeanTrominoes.CompletionPattern.IBricks
