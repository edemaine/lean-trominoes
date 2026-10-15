/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentIntegerSeparator

/-! # Moving boundary bends into the interiors of their permitted cells

Only points on cell boundaries move. Each coordinate changes by at most one
unit after scaling; strict interior vertex coordinates remain exactly scaled.
-/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

def correction (grid value : Int) : Int :=
  if value%grid=0 then if value≤0 then 1 else -1 else 0

def coordinate (grid factor value : Int) : Int := factor*value+correction grid value
def point (grid factor : Int) (p : Cell) : Cell := (coordinate grid factor p.1,coordinate grid factor p.2)

theorem correction_bounds (grid value : Int) : -1≤correction grid value ∧ correction grid value≤1 := by
  unfold correction
  split
  · split <;> omega
  · omega

theorem point_perturbation (grid factor : Int) (p : Cell) :
    GridSegment.PointPerturbation factor p (point grid factor p) := by
  have x := correction_bounds grid p.1
  have y := correction_bounds grid p.2
  simp only [GridSegment.PointPerturbation,point,coordinate,add_sub_cancel_left,abs_le]
  exact ⟨x,y⟩

theorem coordinate_zero (grid factor : Int) : coordinate grid factor 0=1 := by simp [coordinate,correction]

theorem coordinate_positive_boundary {grid factor value : Int} (boundary : value%grid=0) (positive : 0<value) :
    coordinate grid factor value=factor*value-1 := by
  simp [coordinate,correction,boundary,show ¬value≤0 by omega,sub_eq_add_neg]

theorem coordinate_negative_boundary {grid factor value : Int} (boundary : value%grid=0) (negative : value≤0) :
    coordinate grid factor value=factor*value+1 := by simp [coordinate,correction,boundary,negative]

theorem coordinate_interior {grid factor value : Int} (lo : 0<value) (hi : value<grid) :
    coordinate grid factor value=factor*value := by
  have remainder : value%grid=value := Int.emod_eq_of_lt lo.le hi
  simp [coordinate,correction,remainder,show value≠0 by omega]

theorem point_interior {grid factor : Int} {p : Cell}
    (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) : point grid factor p=Cell.scale factor p := by
  simp only [point,coordinate_interior bounds.1 bounds.2.1,coordinate_interior bounds.2.2.1 bounds.2.2.2,Cell.scale]

theorem coordinate_in_zero_cell {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : 0≤value ∧ value≤grid) : 0<coordinate grid factor value ∧ coordinate grid factor value<factor*grid := by
  by_cases zero : value=0
  · subst value
    rw [coordinate_zero]
    have gridStep : 1≤grid := by omega
    constructor <;> nlinarith
  · by_cases top : value=grid
    · subst value
      rw [coordinate_positive_boundary (by simp) gridPositive]
      have gridStep : 1≤grid := by omega
      constructor <;> nlinarith
    · have lo : 0<value := by omega
      have hi : value<grid := by omega
      rw [coordinate_interior lo hi]
      constructor <;> nlinarith

theorem coordinate_in_east_cells {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : 0≤value ∧ value≤2*grid) : 0<coordinate grid factor value ∧ coordinate grid factor value<2*(factor*grid) := by
  have correctionBounds := correction_bounds grid value
  by_cases zero : value=0
  · subst value
    rw [coordinate_zero]
    have gridStep : 1≤grid := by omega
    constructor <;> nlinarith
  · by_cases top : value=2*grid
    · subst value
      rw [coordinate_positive_boundary (by simp) (by omega)]
      have gridStep : 1≤grid := by omega
      constructor <;> nlinarith
    · unfold coordinate
      have lo : 1≤value := by omega
      have hi : value≤2*grid-1 := by omega
      constructor <;> nlinarith

theorem coordinate_in_west_cells {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : -grid≤value ∧ value≤grid) : -factor*grid<coordinate grid factor value ∧ coordinate grid factor value<factor*grid := by
  have correctionBounds := correction_bounds grid value
  by_cases bottom : value= -grid
  · subst value
    rw [coordinate_negative_boundary (by simp) (by omega)]
    have gridStep : 1≤grid := by omega
    constructor <;> nlinarith
  · by_cases top : value=grid
    · subst value
      rw [coordinate_positive_boundary (by simp) gridPositive]
      have gridStep : 1≤grid := by omega
      constructor <;> nlinarith
    · unfold coordinate
      have lo : -grid+1≤value := by omega
      have hi : value≤grid-1 := by omega
      constructor <;> nlinarith

theorem coordinate_off_seams {grid factor value : Int} (_gridPositive : 0<grid) (spacing : 2<factor) :
    coordinate grid factor value%(factor*grid)≠0 := by
  intro onSeam
  obtain ⟨multiple,equation⟩ := Int.dvd_iff_emod_eq_zero.mpr onSeam
  by_cases boundary : value%grid=0
  · have unit : correction grid value=1 ∨ correction grid value= -1 := by
      unfold correction
      rw [if_pos boundary]
      split <;> simp
    have coefficient : factor*(grid*multiple-value)=correction grid value := by
      unfold coordinate at equation
      linear_combination -equation
    have sides : grid*multiple-value≤-1 ∨ grid*multiple-value=0 ∨ 1≤grid*multiple-value := by omega
    rcases sides with negative | zero | positive <;> rcases unit with unit | unit
    all_goals rw [unit] at coefficient
    all_goals nlinarith
  · have noCorrection : correction grid value=0 := by simp [correction,boundary]
    have same : value=grid*multiple := by
      unfold coordinate at equation
      rw [noCorrection] at equation
      have nonzero : factor≠0 := by omega
      apply mul_left_cancel₀ nonzero
      nlinarith [equation]
    simp [same] at boundary

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
