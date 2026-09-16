/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCaps
import LeanTrominoes.TrominoCompletionTranslation
import LeanTrominoes.TrominoCompletionAssembly

/-! # Periodic cap bands and their exact residual strip shape -/
namespace LeanTrominoes.CompletionPattern.StripCaps

def capRegion (t : Tromino) (top : Bool) : Finset Cell := if top then topRegion t else bottomRegion t
def capMotif (t : Tromino) (top : Bool) : List (Placement Unit) := if top then topMotif t else bottomMotif t

theorem cap_tiling (t : Tromino) (top : Bool) :
    IsFiniteTiling (fun _ => t.cells) (capRegion t top) (capMotif t top).toFinset := by
  cases top
  · exact bottom_tiling t
  · exact top_tiling t

def capBand (t : Tromino) (top : Bool) : Set Cell :=
  {c | ∃ i : Int, c ∈ Cell.add (i*width t,0) '' (capRegion t top : Set Cell)}

def capPrefill (t : Tromino) (top : Bool) : Set (Finset Cell) :=
  {f | ∃ i : Int, f ∈ (fun g => g.image (Cell.add (i*width t,0))) ''
    (t.finiteFootprints (capMotif t top).toFinset : Set (Finset Cell))}

theorem cap_region_x (t : Tromino) (top : Bool) {c : Cell} (hc : c ∈ capRegion t top) :
    0 ≤ c.1 ∧ c.1 < width t := by
  cases top <;> simpa only [capRegion,Bool.false_eq_true,if_false,if_true,
    bottomRegion,topRegion,Finset.mem_filter,Finset.mem_product,Finset.mem_Ico] using
    (show 0 ≤ c.1 ∧ c.1 < width t from by
      cases t <;> simp_all [capRegion,topRegion,bottomRegion,width])

theorem cap_copies_separate (t : Tromino) (top : Bool) (i j : Int) (c : Cell)
    (hi : c ∈ Cell.add (i*width t,0) '' (capRegion t top : Set Cell))
    (hj : c ∈ Cell.add (j*width t,0) '' (capRegion t top : Set Cell)) : i = j := by
  obtain ⟨a,ha,ea⟩ := hi
  obtain ⟨b,hb,eb⟩ := hj
  have ba := cap_region_x t top ha
  have bb := cap_region_x t top hb
  have ex := congrArg Prod.fst (ea.trans eb.symm)
  cases t <;> simp only [Cell.add,width] at ex ba bb <;> omega

theorem cap_completable (t : Tromino) (top : Bool) : t.Completable (capBand t top) (capPrefill t top) := by
  have finite := t.completable_of_finiteTiling (capRegion t top) (capMotif t top).toFinset
    (capMotif t top).toFinset (cap_tiling t top) (by rfl)
  exact Tromino.completable_assemble (fun i : Int => finite.translate (i*width t,0))
    (cap_copies_separate t top)

theorem capBand_iff (t : Tromino) (top : Bool) (c : Cell) :
    c ∈ capBand t top ↔ 0 ≤ c.2 ∧ c.2 < 3 ∧
      (if top then c.2 < 2 ∨ c.1 % width t < width t / 2
       else 0 < c.2 ∨ width t / 2 ≤ c.1 % width t) := by
  constructor
  · rintro ⟨i,a,ha,ea⟩
    have ba := cap_region_x t top ha
    have ey := congrArg Prod.snd ea
    have ex := congrArg Prod.fst ea
    have rem : c.1 % width t = a.1 := by
      cases t <;> simp only [width,Cell.add] at ex ba ⊢ <;> omega
    simp only [Cell.add,Int.zero_add] at ey
    rw [rem,← ey]
    cases top <;> simp_all [capRegion,topRegion,bottomRegion,Cell.add]
  · intro hc
    refine ⟨c.1/width t,(c.1%width t,c.2),?_,?_⟩
    · cases t <;> cases top <;> simp_all [capRegion,topRegion,bottomRegion,width] <;> omega
    · apply Prod.ext <;> cases t <;> simp [Cell.add,width] <;> omega

def coreBand (t : Tromino) (height : Int) : Set Cell :=
  {c | 0 ≤ c.2 ∧ c.2 ≤ height ∧
    (c.2 = 0 → width t/2 ≤ c.1%width t) ∧
    (c.2 = height → c.1%width t < width t/2)}

/-- Two cap bands and the translated core exactly partition a horizontal strip. -/
theorem cap_partition (t : Tromino) (height : Int) (hh : 0 < height) (c : Cell) :
    (0 ≤ c.2 ∧ c.2 < height+5) ↔
      c ∈ capBand t true ∨
      Cell.sub c (0,2) ∈ coreBand t height ∨
      Cell.sub c (0,height+2) ∈ capBand t false := by
  rw [capBand_iff,capBand_iff]
  cases t <;> simp [coreBand,Cell.sub,width] <;> omega


theorem cap_occupied (t : Tromino) (top : Bool) :
    Tromino.occupied (capPrefill t top) = capBand t top := by
  have tiled := (isFiniteTiling_iff_isTiling _ _ _).mp (cap_tiling t top)
  ext c
  constructor
  · rintro ⟨f,⟨i,g,hg,rfl⟩,hc⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨i,d,tiled.tilesInside p hp d hd,rfl⟩
  · rintro ⟨i,d,hd,rfl⟩
    obtain ⟨p,⟨hp,hpd⟩,_⟩ := tiled.uniqueCover d hd
    refine ⟨(p.cells (fun _ => t.cells)).image (Cell.add (i*width t,0)),?_,?_⟩
    · exact ⟨i,_,Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨d,hpd,rfl⟩

theorem cap_core_separate (t : Tromino) (height : Int) (hh : 0 < height) (c : Cell) :
    (c ∈ capBand t true → Cell.sub c (0,2) ∉ coreBand t height) ∧
    (c ∈ capBand t true → Cell.sub c (0,height+2) ∉ capBand t false) ∧
    (Cell.sub c (0,2) ∈ coreBand t height → Cell.sub c (0,height+2) ∉ capBand t false) := by
  simp only [capBand_iff]
  cases t <;> simp [coreBand,Cell.sub,width] <;> omega

end LeanTrominoes.CompletionPattern.StripCaps
