/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHeightRedistribution

/-! # Periodic redistribution preserves order relative to integral vertex levels -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem periodicRedistributedHeight_below_vertex {period factor position vertexRow : Int}
    (factorPositive : 0 < factor) (positionBounds : 0 < position ∧ position < period)
    (mapHeight : ℚ → Int) (height : ℚ)
    (rowBounds : 0 < mapHeight (rationalResidue period height) ∧
      mapHeight (rationalResidue period height) < factor*period)
    (finiteBelow : rationalResidue period height < (position : ℚ) →
      mapHeight (rationalResidue period height) < factor*position)
    (below : height < (position : ℚ)+(period : ℚ)*vertexRow) :
    periodicRedistributedHeight period (factor*period) mapHeight height < factor*(position+period*vertexRow) := by
  have periodPositive : 0 < period := by omega
  have cellEq : rationalCell period ((position : ℚ)+(period : ℚ)*vertexRow) = vertexRow := by
    rw [rationalCell_translate periodPositive,rationalCell_of_in_cell periodPositive]
    · simp
    · refine ⟨?_,?_⟩
      · exact_mod_cast positionBounds.1.le
      · exact_mod_cast positionBounds.2
  have cells := rationalCell_monotone periodPositive below.le
  rw [cellEq] at cells
  unfold periodicRedistributedHeight
  rcases lt_or_eq_of_le cells with before | same
  · have outputPositive : 0 < factor*period := mul_pos factorPositive periodPositive
    have gap : factor*period*(rationalCell period height+1) ≤ factor*period*vertexRow := by nlinarith
    have vertexPositive : 0 < factor*position := mul_pos factorPositive positionBounds.1
    nlinarith only [gap,vertexPositive,rowBounds.2]
  · have decomp := rationalCoordinate_decomposition period height
    rw [same] at decomp ⊢
    have finite := finiteBelow (by linarith only [below,decomp])
    nlinarith only [finite]

theorem periodicRedistributedHeight_above_vertex {period factor position vertexRow : Int}
    (factorPositive : 0 < factor) (positionBounds : 0 < position ∧ position < period)
    (mapHeight : ℚ → Int) (height : ℚ)
    (rowBounds : 0 < mapHeight (rationalResidue period height) ∧
      mapHeight (rationalResidue period height) < factor*period)
    (finiteAbove : (position : ℚ) ≤ rationalResidue period height →
      factor*position < mapHeight (rationalResidue period height))
    (above : (position : ℚ)+(period : ℚ)*vertexRow ≤ height) :
    factor*(position+period*vertexRow) < periodicRedistributedHeight period (factor*period) mapHeight height := by
  have periodPositive : 0 < period := by omega
  have cellEq : rationalCell period ((position : ℚ)+(period : ℚ)*vertexRow) = vertexRow := by
    rw [rationalCell_translate periodPositive,rationalCell_of_in_cell periodPositive]
    · simp
    · refine ⟨?_,?_⟩
      · exact_mod_cast positionBounds.1.le
      · exact_mod_cast positionBounds.2
  have cells := rationalCell_monotone periodPositive above
  rw [cellEq] at cells
  unfold periodicRedistributedHeight
  rcases lt_or_eq_of_le cells with after | same
  · have outputPositive : 0 < factor*period := mul_pos factorPositive periodPositive
    have gap : factor*period*(vertexRow+1) ≤ factor*period*rationalCell period height := by nlinarith
    have vertexUpper : factor*position < factor*period := mul_lt_mul_of_pos_left positionBounds.2 factorPositive
    nlinarith only [gap,vertexUpper,rowBounds.1]
  · have decomp := rationalCoordinate_decomposition period height
    rw [← same] at decomp ⊢
    have finite := finiteAbove (by linarith only [above,decomp])
    nlinarith only [finite]

end LeanTrominoes.OrthogonalDrawingRefinement
