/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.StripTrominoPadding
import LeanTrominoes.Periodic
import LeanTrominoes.TilingRegionTranslation
import LeanTrominoes.KeyedStripDisconnected

/-! # Preparing an arbitrary periodic-strip source for the two-tile construction -/

namespace LeanTrominoes.Theorem55StripSource

/-- Enlarge the horizontal period enough to enclose the source height and margins. -/
def period (source : PeriodicStrip) : Nat := (source.width + 72) * source.period

def shifted (source : PeriodicStrip) : Set Cell :=
  {c | Cell.add (0,-10) c ∈ source.carrier}

def region (source : PeriodicStrip) : Set Cell :=
  shifted source ∪ StripTrominoPadding.region (period source)

theorem period_large (source : PeriodicStrip) (positive : 0 < source.period) :
    source.width + 72 ≤ period source := Nat.le_mul_of_pos_right _ positive

theorem shifted_bounds (source : PeriodicStrip) {c : Cell} (hc : c ∈ shifted source) :
    10 ≤ c.2 ∧ c.2 < (source.width : Int) + 10 := by
  have a := hc.1
  have b := hc.2.1
  dsimp [Cell.add] at a b
  omega

theorem padding_disjoint (source : PeriodicStrip) :
    Disjoint (shifted source) (StripTrominoPadding.region (period source)) := by
  apply Set.disjoint_left.mpr
  intro c hs hp
  have a := shifted_bounds source hs
  have b := hp.2
  omega

theorem padding_separated (source : PeriodicStrip) :
    ∀ a ∈ shifted source, ∀ b ∈ StripTrominoPadding.region (period source), ¬ Cell.SideAdjacent a b := by
  intro a ha b hb adjacent
  have ha := shifted_bounds source ha
  have hb := hb.2
  unfold Cell.SideAdjacent at adjacent
  omega

theorem tileable_iff (source : PeriodicStrip) :
    Tromino.I.Tileable (region source) ↔ Tromino.I.Tileable source.carrier := by
  rw [region,i_tileable_union_iff _ _ (padding_disjoint source)
    (padding_separated source) (StripTrominoPadding.tileable _)]
  exact tileable_recenter_region_iff _ _ (0,-10)

theorem source_square (source : PeriodicStrip) (positive : 0 < source.period) :
    ∀ c ∈ PlusRefinement.unitSquare, Cell.add (14,4) c ∈ region source := by
  have large := period_large source positive
  intro c hc
  right
  simp only [PlusRefinement.unitSquare,Finset.mem_insert,Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [StripTrominoPadding.region,Cell.add,
      Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 14) (by omega : (14 : Int) < period source),
      Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 15) (by omega : (15 : Int) < period source)]

theorem region_bounds (source : PeriodicStrip) (positive : 0 < source.period)
    {c : Cell} (hc : c ∈ region source) : 4 ≤ c.2 ∧ c.2 < (period source : Int) - 6 := by
  have large := period_large source positive
  rcases hc with hs | hp
  · have hs := shifted_bounds source hs
    omega
  · have hp := hp.2
    omega

theorem translate_carrier (source : PeriodicStrip) (x : Int)
    (multiple : (source.period : Int) ∣ x) (c : Cell) :
    Cell.add (x,0) c ∈ source.carrier ↔ c ∈ source.carrier := by
  rw [source.mem_carrier_iff,source.mem_carrier_iff]
  simp only [Cell.add,zero_add]
  have eq (base : Cell) : x + c.1 - base.1 = x + (c.1 - base.1) := by omega
  have divisible (y : Int) : (source.period : Int) ∣ x+y ↔ (source.period : Int) ∣ y := by
    obtain ⟨k,hk⟩ := multiple
    constructor
    · rintro ⟨l,hl⟩
      refine ⟨l-k,?_⟩
      rw [mul_sub]
      omega
    · rintro ⟨l,hl⟩
      exact ⟨k+l,by rw [mul_add]; omega⟩
  simp only [eq,divisible]

theorem translate_region (source : PeriodicStrip) (i : Int) (c : Cell) :
    Cell.add ((period source : Int)*i,0) c ∈ region source ↔ c ∈ region source := by
  have multiple : (source.period : Int) ∣ (period source : Int)*i := by
    refine ⟨((source.width : Int)+72)*i,?_⟩
    simp [period,Nat.cast_add,Nat.cast_mul]
    ring
  have shift_eq : Cell.add (0,-10) (Cell.add ((period source : Int)*i,0) c) =
      Cell.add ((period source : Int)*i,0) (Cell.add (0,-10) c) := by simp [Cell.add]
  change (_ ∈ shifted source ∨ _ ∈ StripTrominoPadding.region _) ↔ _
  simp only [shifted,Set.mem_setOf_eq,shift_eq,translate_carrier source _ multiple]
  simp [region,shifted,StripTrominoPadding.region,Cell.add,Int.add_emod]

end LeanTrominoes.Theorem55StripSource
