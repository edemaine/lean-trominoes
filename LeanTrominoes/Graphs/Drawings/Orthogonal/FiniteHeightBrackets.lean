/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! # Consecutive integer levels bracketing a rational crossing height -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def lowerLevels (levels : Finset Int) (height : ℚ) : Finset Int := levels.filter (fun level => (level : ℚ) ≤ height)
def upperLevels (levels : Finset Int) (height : ℚ) : Finset Int := levels.filter (fun level => height < (level : ℚ))

def lowerHeight (levels : Finset Int) (height : ℚ) : Int :=
  if present : (lowerLevels levels height).Nonempty then (lowerLevels levels height).max' present else 0

def upperHeight (levels : Finset Int) (height : ℚ) : Int :=
  if present : (upperLevels levels height).Nonempty then (upperLevels levels height).min' present else 0

theorem lowerHeight_spec {levels : Finset Int} {height : ℚ} (present : (lowerLevels levels height).Nonempty) :
    lowerHeight levels height ∈ levels ∧ (lowerHeight levels height : ℚ) ≤ height ∧
      ∀ level ∈ levels, (level : ℚ) ≤ height → level ≤ lowerHeight levels height := by
  have member := Finset.max'_mem (lowerLevels levels height) present
  have data := Finset.mem_filter.mp member
  simp only [lowerHeight,dif_pos present]
  exact ⟨data.1,data.2,fun level member below => Finset.le_max' _ level (Finset.mem_filter.mpr ⟨member,below⟩)⟩

theorem upperHeight_spec {levels : Finset Int} {height : ℚ} (present : (upperLevels levels height).Nonempty) :
    upperHeight levels height ∈ levels ∧ height < (upperHeight levels height : ℚ) ∧
      ∀ level ∈ levels, height < (level : ℚ) → upperHeight levels height ≤ level := by
  have member := Finset.min'_mem (upperLevels levels height) present
  have data := Finset.mem_filter.mp member
  simp only [upperHeight,dif_pos present]
  exact ⟨data.1,data.2,fun level member above => Finset.min'_le _ level (Finset.mem_filter.mpr ⟨member,above⟩)⟩

theorem height_bracket_ordered {levels : Finset Int} {height : ℚ}
    (lowerPresent : (lowerLevels levels height).Nonempty) (upperPresent : (upperLevels levels height).Nonempty) :
    lowerHeight levels height < upperHeight levels height := by
  have ordered := lt_of_le_of_lt (lowerHeight_spec lowerPresent).2.1 (upperHeight_spec upperPresent).2.1
  exact_mod_cast ordered

theorem height_bracket_no_level_between {levels : Finset Int} {height : ℚ}
    (lowerPresent : (lowerLevels levels height).Nonempty) (upperPresent : (upperLevels levels height).Nonempty)
    {level : Int} (member : level ∈ levels) :
    ¬(lowerHeight levels height < level ∧ level < upperHeight levels height) := by
  intro inside
  by_cases below : (level : ℚ) ≤ height
  · have bound := (lowerHeight_spec lowerPresent).2.2 level member below
    omega
  · have bound := (upperHeight_spec upperPresent).2.2 level member (lt_of_not_ge below)
    omega

theorem height_bracket_monotone {levels : Finset Int} {first second : ℚ} (ordered : first ≤ second)
    (firstLower : (lowerLevels levels first).Nonempty) (firstUpper : (upperLevels levels first).Nonempty)
    (secondLower : (lowerLevels levels second).Nonempty) (secondUpper : (upperLevels levels second).Nonempty) :
    lowerHeight levels first ≤ lowerHeight levels second ∧ upperHeight levels first ≤ upperHeight levels second := by
  have fl := lowerHeight_spec firstLower
  have su := upperHeight_spec secondUpper
  exact ⟨(lowerHeight_spec secondLower).2.2 _ fl.1 (fl.2.1.trans ordered),
    (upperHeight_spec firstUpper).2.2 _ su.1 (lt_of_le_of_lt ordered su.2.1)⟩

theorem height_brackets_same_or_separated {levels : Finset Int} {first second : ℚ} (ordered : first ≤ second)
    (firstLower : (lowerLevels levels first).Nonempty) (firstUpper : (upperLevels levels first).Nonempty)
    (secondLower : (lowerLevels levels second).Nonempty) (secondUpper : (upperLevels levels second).Nonempty) :
    (lowerHeight levels first = lowerHeight levels second ∧ upperHeight levels first = upperHeight levels second) ∨
      upperHeight levels first ≤ lowerHeight levels second := by
  have monotone := height_bracket_monotone ordered firstLower firstUpper secondLower secondUpper
  have firstBracket := height_bracket_ordered firstLower firstUpper
  have secondBracket := height_bracket_ordered secondLower secondUpper
  by_cases sameLower : lowerHeight levels first = lowerHeight levels second
  · left
    refine ⟨sameLower,?_⟩
    have member := (upperHeight_spec firstUpper).1
    by_cases below : (upperHeight levels first : ℚ) ≤ second
    · have bound := (lowerHeight_spec secondLower).2.2 _ member below
      omega
    · have bound := (upperHeight_spec secondUpper).2.2 _ member (lt_of_not_ge below)
      omega
  · right
    have noBetween := height_bracket_no_level_between firstLower firstUpper (lowerHeight_spec secondLower).1
    omega

theorem height_bracket_present_in_cell {levels : Finset Int} {grid : Int} (zero : 0 ∈ levels) (top : grid ∈ levels)
    {height : ℚ} (bounds : 0 ≤ height ∧ height < grid) :
    (lowerLevels levels height).Nonempty ∧ (upperLevels levels height).Nonempty :=
  ⟨⟨0,Finset.mem_filter.mpr ⟨zero,by simpa using bounds.1⟩⟩,
    ⟨grid,Finset.mem_filter.mpr ⟨top,bounds.2⟩⟩⟩

end LeanTrominoes.OrthogonalDrawingRefinement
