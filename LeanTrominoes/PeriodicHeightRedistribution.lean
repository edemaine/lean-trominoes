/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalPeriodicCoordinates

/-! # Extending a finite crossing redistribution periodically across all rows -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def periodicRedistributedHeight (period outputPeriod : Int) (mapHeight : ℚ → Int) (height : ℚ) : Int :=
  outputPeriod*rationalCell period height+mapHeight (rationalResidue period height)

theorem periodicRedistributedHeight_translate {period : Int} (positive : 0 < period)
    (outputPeriod : Int) (mapHeight : ℚ → Int) (height : ℚ) (shift : Int) :
    periodicRedistributedHeight period outputPeriod mapHeight (height+(period : ℚ)*shift) =
      periodicRedistributedHeight period outputPeriod mapHeight height+outputPeriod*shift := by
  unfold periodicRedistributedHeight
  rw [rationalCell_translate positive,rationalResidue_translate positive]
  ring

theorem periodicRedistributedHeight_in_cell {period : Int} (positive : 0 < period)
    (outputPeriod : Int) (mapHeight : ℚ → Int) {height : ℚ} (bounds : 0 ≤ height ∧ height < period) :
    periodicRedistributedHeight period outputPeriod mapHeight height = mapHeight height := by
  simp [periodicRedistributedHeight,rationalCell_of_in_cell positive bounds,rationalResidue_of_in_cell positive bounds]

theorem periodicRedistributedHeight_bounds {period outputPeriod : Int} (mapHeight : ℚ → Int) (height : ℚ)
    (bounds : 0 < mapHeight (rationalResidue period height) ∧ mapHeight (rationalResidue period height) < outputPeriod) :
    outputPeriod*rationalCell period height < periodicRedistributedHeight period outputPeriod mapHeight height ∧
      periodicRedistributedHeight period outputPeriod mapHeight height < outputPeriod*(rationalCell period height+1) := by
  unfold periodicRedistributedHeight
  constructor <;> nlinarith

theorem periodicRedistributedHeight_preserves_order {period outputPeriod : Int} (positive : 0 < period)
    (outputPositive : 0 < outputPeriod) (mapHeight : ℚ → Int) (heights : Finset ℚ)
    (mapOrder : StrictMonoOn mapHeight heights) (mapBounds : ∀ height ∈ heights, 0 < mapHeight height ∧ mapHeight height < outputPeriod)
    {first second : ℚ} (firstMember : rationalResidue period first ∈ heights) (secondMember : rationalResidue period second ∈ heights)
    (ordered : first < second) :
    periodicRedistributedHeight period outputPeriod mapHeight first < periodicRedistributedHeight period outputPeriod mapHeight second := by
  have cells := rationalCell_monotone positive ordered.le
  rcases lt_or_eq_of_le cells with increasing | same
  · have firstBounds := periodicRedistributedHeight_bounds mapHeight first (mapBounds _ firstMember)
    have secondBounds := periodicRedistributedHeight_bounds mapHeight second (mapBounds _ secondMember)
    have scaled : outputPeriod*(rationalCell period first+1) ≤ outputPeriod*rationalCell period second := by nlinarith
    omega
  · have firstDecomp := rationalCoordinate_decomposition period first
    have secondDecomp := rationalCoordinate_decomposition period second
    rw [← same] at secondDecomp
    have residues : rationalResidue period first < rationalResidue period second := by linarith
    have mapped := mapOrder firstMember secondMember residues
    unfold periodicRedistributedHeight
    rw [same]
    omega

end LeanTrominoes.OrthogonalDrawingRefinement
