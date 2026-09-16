/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCapBands
import LeanTrominoes.TrominoCompletionShell

/-! # Exact completion equivalence between a brick core and its capped strip -/
namespace LeanTrominoes.CompletionPattern.StripCaps

theorem mem_translate_iff (region : Set Cell) (v c : Cell) :
    c ∈ Cell.add v '' region ↔ Cell.sub c v ∈ region := by
  constructor
  · rintro ⟨d,hd,rfl⟩
    simpa [Cell.sub,Cell.add] using hd
  · intro hc
    refine ⟨Cell.sub c v,hc,?_⟩
    apply Prod.ext <;> simp [Cell.add,Cell.sub]

def shellRegion (t : Tromino) (height : Int) : Set Cell :=
  (Cell.add (0,-2) '' capBand t true) ∪ (Cell.add (0,height) '' capBand t false)

def shellPrefill (t : Tromino) (height : Int) : Set (Finset Cell) :=
  ((fun f => f.image (Cell.add (0,-2))) '' capPrefill t true) ∪
    ((fun f => f.image (Cell.add (0,height))) '' capPrefill t false)

def cappedRegion (height : Int) : Set Cell := {c | -2 ≤ c.2 ∧ c.2 < height+3}

theorem shell_disjoint (t : Tromino) (height : Int) (hh : 0 < height) :
    Disjoint (Cell.add (0,-2) '' capBand t true) (Cell.add (0,height) '' capBand t false) := by
  apply Set.disjoint_left.mpr
  intro c ht hb
  rw [mem_translate_iff,capBand_iff] at ht hb
  simp only [Cell.sub] at ht hb
  omega

theorem shell_completable (t : Tromino) (height : Int) (hh : 0 < height) :
    t.Completable (shellRegion t height) (shellPrefill t height) :=
  ((cap_completable t true).translate (0,-2)).union
    ((cap_completable t false).translate (0,height)) (shell_disjoint t height hh)

theorem shell_occupied (t : Tromino) (height : Int) :
    Tromino.occupied (shellPrefill t height) = shellRegion t height := by
  rw [shellPrefill,Tromino.occupied_union,Tromino.occupied_translate,Tromino.occupied_translate,
    cap_occupied,cap_occupied]
  rfl

theorem core_shell_region (t : Tromino) (height : Int) (hh : 0 < height) :
    coreBand t height ∪ shellRegion t height = cappedRegion height := by
  ext c
  simp only [shellRegion,Set.mem_union,mem_translate_iff,capBand_iff]
  cases t <;> simp [coreBand,cappedRegion,Cell.sub,width] <;> omega

theorem core_shell_disjoint (t : Tromino) (height : Int) (hh : 0 < height) :
    Disjoint (coreBand t height) (shellRegion t height) := by
  apply Set.disjoint_left.mpr
  intro c hc hs
  simp only [shellRegion,Set.mem_union,mem_translate_iff,capBand_iff] at hs
  cases t <;> simp [coreBand,Cell.sub,width] at hc hs <;> omega

/-- No assumption about the periodicity of the completing tiling is needed. -/
theorem capped_completion_iff (t : Tromino) (height : Int) (hh : 0 < height)
    (prescribed : Set (Finset Cell))
    (inside : ∀ f ∈ prescribed, ∀ c ∈ f, c ∈ coreBand t height) :
    t.Completable (cappedRegion height) (prescribed ∪ shellPrefill t height) ↔
      t.Completable (coreBand t height) prescribed := by
  rw [← core_shell_region t height hh]
  exact Tromino.completable_attach_filled_iff (shell_completable t height hh)
    (shell_occupied t height) (core_shell_disjoint t height hh) inside

end LeanTrominoes.CompletionPattern.StripCaps
