/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationStripCompiler
import LeanTrominoes.CompletionLPrefillValidity
import LeanTrominoes.CompletionIPrefillValidity

/-! # Every strip-reduction output is a valid partial tiling -/
namespace LeanTrominoes
namespace Tromino

private theorem IsPartialTiling.union {t : Tromino} {r s : Set Cell} {a b : Set (Finset Cell)}
    (ha : t.IsPartialTiling r a) (hb : t.IsPartialTiling s b) (disj : Disjoint r s) :
    t.IsPartialTiling (r ∪ s) (a ∪ b) := by
  refine ⟨?_,?_⟩
  · intro f hf
    rcases hf with hf | hf
    · exact ⟨(ha.tilesInside f hf).1,fun c hc => Or.inl ((ha.tilesInside f hf).2 c hc)⟩
    · exact ⟨(hb.tilesInside f hf).1,fun c hc => Or.inr ((hb.tilesInside f hf).2 c hc)⟩
  · intro f hf g hg c hc hgc
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact ha.nonoverlap f hf g hg c hc hgc
    · exact False.elim (Set.disjoint_left.mp disj ((ha.tilesInside f hf).2 c hc) ((hb.tilesInside g hg).2 c hgc))
    · exact False.elim (Set.disjoint_left.mp disj ((ha.tilesInside g hg).2 c hgc) ((hb.tilesInside f hf).2 c hc))
    · exact hb.nonoverlap f hf g hg c hc hgc

private theorem IsPartialTiling.translate {t : Tromino} {r : Set Cell} {a : Set (Finset Cell)}
    (h : t.IsPartialTiling r a) (v : Cell) :
    t.IsPartialTiling (Cell.add v '' r) ((fun f => f.image (Cell.add v)) '' a) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨f,hf,rfl⟩
    refine ⟨(h.tilesInside f hf).1.translate v,?_⟩
    intro c hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨d,(h.tilesInside f hf).2 d hd,rfl⟩
  · rintro _ ⟨f,hf,rfl⟩ _ ⟨g,hg,rfl⟩ c hc hgc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hgc
    have same := Cell.add_left_injective v eq
    subst e
    rw [h.nonoverlap f hf g hg d hd he]
end Tromino
namespace CompletionPattern

private theorem capped_partial {t : Tromino} {height : Int} (hh : 0 < height)
    {prescribed : Set (Finset Cell)} (core : t.IsPartialTiling (StripCaps.coreBand t height) prescribed) :
    t.IsPartialTiling (StripCaps.cappedRegion height) (prescribed ∪ StripCaps.shellPrefill t height) := by
  obtain ⟨tiles,valid,contains⟩ := StripCaps.shell_completable t height hh
  have combined := core.union (valid.partial contains) (StripCaps.core_shell_disjoint t height hh)
  rwa [StripCaps.core_shell_region t height hh] at combined

theorem LBricks.compileStrip_valid (period count : Nat) (hp : 0 < period) (hn : 0 < count)
    (palette : Cell → Fin 24)
    (periodic : ∀ c (i : Int), palette (c.1+i*period,c.2) = palette c) :
    Tromino.L.IsPartialTiling (LBricks.compileStrip period count palette).region
      ((LBricks.compileStrip period count palette).periodic.prescribed .L) := by
  have subset : LBricks.bandPrescribed palette count ⊆ LBricks.globalPrescribed palette := by
    rw [← LBricks.band_exterior_prescribed palette count]
    exact Set.subset_union_left
  have global := LBricks.global_prefill_valid palette
  have core : Tromino.L.IsPartialTiling (StripCaps.coreBand .L (36*count)) (LBricks.bandPrescribed palette count) :=
    ⟨fun f hf => ⟨(global.tilesInside f (subset hf)).1,LBricks.band_prescribed_inside palette count f hf⟩,
      fun f hf g hg c hc hgc => global.nonoverlap f (subset hf) g (subset hg) c hc hgc⟩
  rw [LBricks.compileStrip_prescribed period count hp palette periodic,LBricks.compileStrip_region]
  exact (capped_partial (by exact_mod_cast (show 0 < 36*count by omega)) core).translate (0,2)

theorem IBricks.compileStrip_valid (period count : Nat) (hp : 0 < period) (hn : 0 < count)
    (palette : Cell → Fin 24)
    (periodic : ∀ c (i : Int), palette (c.1+i*period,c.2) = palette c) :
    Tromino.I.IsPartialTiling (IBricks.compileStrip period count palette).region
      ((IBricks.compileStrip period count palette).periodic.prescribed .I) := by
  have subset : IBricks.bandPrescribed palette count ⊆ IBricks.globalPrescribed palette := by
    rw [← IBricks.band_exterior_prescribed palette count]
    exact Set.subset_union_left
  have global := IBricks.global_prefill_valid palette
  have core : Tromino.I.IsPartialTiling (StripCaps.coreBand .I (162*count)) (IBricks.bandPrescribed palette count) :=
    ⟨fun f hf => ⟨(global.tilesInside f (subset hf)).1,IBricks.band_prescribed_inside palette count f hf⟩,
      fun f hf g hg c hc hgc => global.nonoverlap f (subset hf) g (subset hg) c hc hgc⟩
  rw [IBricks.compileStrip_prescribed period count hp palette periodic,IBricks.compileStrip_region]
  exact (capped_partial (by exact_mod_cast (show 0 < 162*count by omega)) core).translate (0,2)

/-- Validity holds even for unsatisfiable source drawings. -/
theorem StripOrientation.compile_valid (t : Tromino) (d : Gadget.PeriodicOrthogonalDrawing) :
    t.IsPartialTiling (compile t d).region ((compile t d).periodic.prescribed t) := by
  have hp : 0 < period d := by simp [period,Gadget.PeriodicOrthogonalDrawing.horizontalPeriod]
  have hn : 0 < count d := by simp [count]
  cases t
  · exact IBricks.compileStrip_valid _ _ hp hn _ (palette_periodic d)
  · exact LBricks.compileStrip_valid _ _ hp hn _ (palette_periodic d)
end CompletionPattern
end LeanTrominoes
