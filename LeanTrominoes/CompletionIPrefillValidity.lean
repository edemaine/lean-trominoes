/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIPrefillGeometry
import LeanTrominoes.CompletionIGuardedRelations
import LeanTrominoes.TrominoCompletionTranslation

/-! # Guarded I prefills are valid independently of satisfiability -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

theorem Atom.fixed_disjoint_boundary (a : Atom) : Disjoint a.fixed a.boundary := by
  cases a <;> decide +kernel

theorem Atom.prefill_tiled (a : Atom) :
    IsFiniteTiling (fun _ => Tromino.I.cells) a.fixed a.pattern.prefill := by
  rw [a.fixed_eq]
  cases a
  · exact IGuardedEqBoundary.prefill_checked
  · exact IGuardedNegBoundary.prefill_checked
  · exact IGuardedPlugTopBoundary.prefill_checked
  · exact IGuardedPlugBotBoundary.prefill_checked
  · exact IGuardedDup.prefill_checked
  · exact IGuardedTftsat.prefill_checked

theorem Atom.prefill_nonoverlap (a : Atom) {p q : Placement Unit} (hp : p ∈ a.motif) (hq : q ∈ a.motif)
    {c : Cell} (hc : c ∈ p.cells (fun _ => Tromino.I.cells)) (hc' : c ∈ q.cells (fun _ => Tromino.I.cells)) :
    p.cells (fun _ => Tromino.I.cells) = q.cells (fun _ => Tromino.I.cells) := by
  have completion := Tromino.I.completable_of_finiteTiling a.fixed a.pattern.prefill a.pattern.prefill
    a.prefill_tiled (Finset.Subset.refl _)
  have prefillValid := ((Tromino.I.completable_iff _ _).mp completion).1
  exact prefillValid.nonoverlap _ (Finset.mem_image.mpr ⟨p,(a.prefill_mem p).mpr hp,rfl⟩)
    _ (Finset.mem_image.mpr ⟨q,(a.prefill_mem q).mpr hq,rfl⟩) c hc hc'

theorem global_prefill_valid (palette : Cell → Fin 24) :
    Tromino.I.IsPartialTiling Set.univ (globalPrescribed palette) := by
  constructor
  · intro f hf
    exact ⟨global_prescribed_legal palette hf,fun _ _ => trivial⟩
  · intro f hf g hg c hc hgc
    obtain ⟨location,entry,he,p,hp,rfl⟩ := prescribed_atom palette hf
    rw [Placement.shift_cells_image] at hc
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hc
    have fixed := (entry.1.fixed_mem d).mpr ⟨p,hp,hd⟩
    have interior : d ∈ entry.1.pattern.region \ entry.1.boundary :=
      Finset.mem_sdiff.mpr ⟨entry.1.fixed_inside fixed,
        fun member => Finset.disjoint_left.mp entry.1.fixed_disjoint_boundary fixed member⟩
    have cover : Cell.add (atomOffset location entry) d ∈ g := by rwa [eq]
    obtain ⟨q,hq,rfl⟩ := prescribed_core_owner palette location he hg interior cover
    have hqCover := (Placement.mem_shift_cells (fun _ => Tromino.I.cells) (atomOffset location entry) q d).mp cover
    rw [Placement.shift_cells_image,Placement.shift_cells_image,entry.1.prefill_nonoverlap hp hq hd hqCover]

end LeanTrominoes.CompletionPattern.IBricks
