/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLPrefillGeometry
import LeanTrominoes.CompletionLNoCrossing
import LeanTrominoes.TrominoCompletionRestriction

/-! # Restricting arbitrary plane completions to individual L subbricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def atomPrescribed (location : Cell) (entry : Atom × Cell) : Set (Finset Cell) :=
  {f | ∃ p ∈ entry.1.motif,
    f = (p.shift (atomOffset location entry)).cells (fun _ => Tromino.L.cells)}

/-- Neither new nor prescribed tiles in a full completion can cross a
subbrick boundary while touching its interior. -/
theorem completed_tile_contained (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.L.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed)
    {f : Finset Cell} (hf : f ∈ completed) {c : Cell}
    (hc : c ∈ entry.1.pattern.region \ entry.1.boundary)
    (covers : Cell.add (atomOffset location entry) c ∈ f) :
    f ⊆ entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  by_cases prescribed : f ∈ globalPrescribed palette
  · obtain ⟨p,hp,rfl⟩ := prescribed_core_owner palette location he prescribed hc covers
    exact shifted_motif_inside location entry hp
  · have avoids : ∀ d ∈ f, d ∉ globalFilled palette := by
      intro d hd filled
      obtain ⟨g,hg,hgd⟩ := filled
      have eq := (h.partial (Set.Subset.refl completed)).nonoverlap
        f hf g (retained hg) d hd hgd
      exact prescribed (eq ▸ hg)
    have notFixed : c ∉ entry.1.fixed := by
      intro fixed
      exact avoids _ covers (atom_barrier_global palette location he (Finset.mem_union_left _ fixed))
    have core : c ∈ entry.1.core :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,notFixed⟩,
        (Finset.mem_sdiff.mp hc).2⟩
    exact residual_tile_contained palette location he (h.tilesInside f hf).1 avoids core covers

/-- A plane completion induces a local completion at every subbrick,
with only connector cells assigned to neighboring subbricks. -/
theorem local_completion_of_global (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    (global : Tromino.L.Completable Set.univ (globalPrescribed palette)) :
    ∃ outside : Finset Cell,
      outside ⊆ entry.1.boundary.image (Cell.add (atomOffset location entry)) ∧
      Tromino.L.Completable
        (entry.1.pattern.region.image (Cell.add (atomOffset location entry)) \ outside : Finset Cell)
        (atomPrescribed location entry) := by
  obtain ⟨completed,h,retained⟩ := global
  apply h.local_completion
    (entry.1.pattern.region.image (Cell.add (atomOffset location entry)))
    (entry.1.boundary.image (Cell.add (atomOffset location entry))) (atomPrescribed location entry)
  · exact Set.subset_univ _
  · rintro f ⟨p,hp,rfl⟩
    exact retained (atom_prescribed palette location he hp)
  · rintro f ⟨p,hp,rfl⟩
    exact shifted_motif_inside location entry hp
  · intro f hf c hfc hc
    obtain ⟨inside,notBoundary⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp inside
    apply completed_tile_contained palette location he h retained hf _ hfc
    exact Finset.mem_sdiff.mpr ⟨hd,fun hb => notBoundary (Finset.mem_image.mpr ⟨d,hb,rfl⟩)⟩

end LeanTrominoes.CompletionPattern.LBricks
