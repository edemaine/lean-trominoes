/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion

/-! # Finite tiling certificates that retain a prescribed prefill -/

namespace LeanTrominoes.Tromino

/-- Forget representation-level distinctions among finitely many placements. -/
def finiteFootprints (t : Tromino) (ps : Finset (Placement Unit)) : Finset (Finset Cell) :=
  ps.image (Placement.cells (fun _ => t.cells))

theorem completable_of_finiteTiling (t : Tromino) (region : Finset Cell)
    (prefill completed : Finset (Placement Unit))
    (tiled : IsFiniteTiling (fun _ => t.cells) region completed)
    (retained : prefill ⊆ completed) :
    t.Completable (region : Set Cell) (t.finiteFootprints prefill : Set (Finset Cell)) := by
  have h := (isFiniteTiling_iff_isTiling _ _ _).mp tiled
  refine ⟨(t.finiteFootprints completed : Set (Finset Cell)),⟨?_,?_⟩,?_⟩
  · intro f hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨⟨p,rfl⟩,fun c hc => h.tilesInside p hp c hc⟩
  · intro c hc
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := h.uniqueCover c hc
    refine ⟨p.cells (fun _ => t.cells),⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,hpc⟩,?_⟩
    intro g hg
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hg.1
    have covers : c ∈ q.cells (fun _ => t.cells) := eq ▸ hg.2
    have same := unique q ⟨hq,covers⟩
    exact eq.symm.trans (congrArg (Placement.cells (fun _ => t.cells)) same)
  · intro f hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_image.mpr ⟨p,retained hp,rfl⟩

end LeanTrominoes.Tromino
