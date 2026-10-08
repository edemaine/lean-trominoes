/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-! # Integer cut strips and the intervening open slabs exhaust the rational line -/
namespace LeanTrominoes.RationalIntegerStripCover

def CutContains (epsilon : ℚ) (line : Int) (coordinate : ℚ) : Prop :=
  (line : ℚ)-epsilon ≤ coordinate ∧ coordinate ≤ (line : ℚ)+epsilon

def SlabInteriorContains (epsilon : ℚ) (column : Int) (coordinate : ℚ) : Prop :=
  (column : ℚ)+epsilon < coordinate ∧ coordinate < (column : ℚ)+1-epsilon

theorem cut_or_slab {epsilon coordinate : ℚ} (positive : 0 < epsilon) :
    (∃ line : Int, CutContains epsilon line coordinate) ∨
      (∃ column : Int, SlabInteriorContains epsilon column coordinate) := by
  let column := ⌊coordinate⌋
  have lower : (column : ℚ) ≤ coordinate := Int.floor_le coordinate
  have upper : coordinate < (column : ℚ)+1 := Int.lt_floor_add_one coordinate
  by_cases nearLeft : coordinate ≤ (column : ℚ)+epsilon
  · exact Or.inl ⟨column,by constructor <;> linarith⟩
  by_cases nearRight : (column : ℚ)+1-epsilon ≤ coordinate
  · left
    refine ⟨column+1,?_,?_⟩ <;> push_cast <;> linarith
  · exact Or.inr ⟨column,lt_of_not_ge nearLeft,lt_of_not_ge nearRight⟩

theorem cut_line_unique {epsilon coordinate : ℚ} (small : epsilon < 1/2)
    {first last : Int} (firstContains : CutContains epsilon first coordinate)
    (lastContains : CutContains epsilon last coordinate) : first = last := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · have gap : (first : ℚ)+1 ≤ last := by exact_mod_cast (by omega : first+1 ≤ last)
    linarith [firstContains.2,lastContains.1]
  · have gap : (last : ℚ)+1 ≤ first := by exact_mod_cast (by omega : last+1 ≤ first)
    linarith [lastContains.2,firstContains.1]

theorem slab_column_unique {epsilon coordinate : ℚ} (nonnegative : 0 ≤ epsilon)
    {first last : Int} (firstContains : SlabInteriorContains epsilon first coordinate)
    (lastContains : SlabInteriorContains epsilon last coordinate) : first = last := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · have gap : (first : ℚ)+1 ≤ last := by exact_mod_cast (by omega : first+1 ≤ last)
    linarith [firstContains.2,lastContains.1]
  · have gap : (last : ℚ)+1 ≤ first := by exact_mod_cast (by omega : last+1 ≤ first)
    linarith [lastContains.2,firstContains.1]

theorem cut_slab_disjoint {epsilon coordinate : ℚ} {line column : Int}
    (cut : CutContains epsilon line coordinate) (slab : SlabInteriorContains epsilon column coordinate) : False := by
  have positions : line ≤ column ∨ column+1 ≤ line := by omega
  rcases positions with before | after
  · have bound : (line : ℚ) ≤ column := by exact_mod_cast before
    linarith [cut.2,slab.1]
  · have bound : (column : ℚ)+1 ≤ line := by exact_mod_cast after
    linarith [cut.1,slab.2]

theorem cut_strict_between_endpoints {epsilon coordinate : ℚ}
    {source target line : Int} (cut : CutContains epsilon line coordinate)
    (awaySource : (source : ℚ)+epsilon < coordinate) (awayTarget : coordinate < (target : ℚ)-epsilon) :
    source < line ∧ line < target := by
  constructor
  · by_contra notAfter
    have bound : (line : ℚ) ≤ source := by exact_mod_cast (le_of_not_gt notAfter)
    linarith [cut.2]
  · by_contra notBefore
    have bound : (target : ℚ) ≤ line := by exact_mod_cast (le_of_not_gt notBefore)
    linarith [cut.1]

def RowInteriorContains (period delta : ℚ) (row : Int) (coordinate : ℚ) : Prop :=
  period*row-delta < coordinate ∧ coordinate < period*((row : ℚ)+1)-delta

theorem row_unique {period delta coordinate : ℚ} (positive : 0 < period)
    {first last : Int} (firstContains : RowInteriorContains period delta first coordinate)
    (lastContains : RowInteriorContains period delta last coordinate) : first = last := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · have gap : (first : ℚ)+1 ≤ last := by exact_mod_cast (by omega : first+1 ≤ last)
    have scaled := mul_le_mul_of_nonneg_left gap positive.le
    linarith [firstContains.2,lastContains.1]
  · have gap : (last : ℚ)+1 ≤ first := by exact_mod_cast (by omega : last+1 ≤ first)
    have scaled := mul_le_mul_of_nonneg_left gap positive.le
    linarith [lastContains.2,firstContains.1]

def SlabContains (epsilon : ℚ) (column : Int) (coordinate : ℚ) : Prop :=
  (column : ℚ)+epsilon ≤ coordinate ∧ coordinate ≤ (column : ℚ)+1-epsilon

theorem closed_slab_column_unique {epsilon coordinate : ℚ} (positive : 0 < epsilon)
    {first last : Int} (firstContains : SlabContains epsilon first coordinate)
    (lastContains : SlabContains epsilon last coordinate) : first = last := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · have gap : (first : ℚ)+1 ≤ last := by exact_mod_cast (by omega : first+1 ≤ last)
    linarith [firstContains.2,lastContains.1]
  · have gap : (last : ℚ)+1 ≤ first := by exact_mod_cast (by omega : last+1 ≤ first)
    linarith [lastContains.2,firstContains.1]

def RowContains (period delta : ℚ) (row : Int) (coordinate : ℚ) : Prop :=
  period*row-delta ≤ coordinate ∧ coordinate ≤ period*((row : ℚ)+1)-delta

theorem closed_row_contact_cases {period delta coordinate : ℚ} (positive : 0 < period)
    {first last : Int} (firstContains : RowContains period delta first coordinate)
    (lastContains : RowContains period delta last coordinate) :
    first = last ∨
      (last = first+1 ∧ coordinate = period*last-delta) ∨
      (first = last+1 ∧ coordinate = period*first-delta) := by
  unfold RowContains at firstContains lastContains
  rcases lt_trichotomy first last with before | same | after
  · have adjacent : last = first+1 := by
      by_contra notAdjacent
      have gap : (first : ℚ)+2 ≤ last := by exact_mod_cast (by omega : first+2 ≤ last)
      have scaled := mul_le_mul_of_nonneg_left gap positive.le
      linarith [firstContains.2,lastContains.1]
    refine Or.inr (Or.inl ⟨adjacent,?_⟩)
    rw [adjacent] at lastContains ⊢
    push_cast at lastContains ⊢
    linarith [firstContains.2,lastContains.1]
  · exact Or.inl same
  · have adjacent : first = last+1 := by
      by_contra notAdjacent
      have gap : (last : ℚ)+2 ≤ first := by exact_mod_cast (by omega : last+2 ≤ first)
      have scaled := mul_le_mul_of_nonneg_left gap positive.le
      linarith [lastContains.2,firstContains.1]
    refine Or.inr (Or.inr ⟨adjacent,?_⟩)
    rw [adjacent] at firstContains ⊢
    push_cast at firstContains ⊢
    linarith [lastContains.2,firstContains.1]

end LeanTrominoes.RationalIntegerStripCover
