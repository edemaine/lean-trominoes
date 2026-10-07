/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHeightRedistribution
import Mathlib.Tactic

/-! # Finite row clearance extends to every periodic vertex translate -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem periodicRedistributedHeight_vertex_clearance {period factor margin position vertexRow : Int}
    (factorPositive : 0 < factor) (marginNonnegative : 0 ≤ margin) (positionBounds : 0 < position ∧ position < period)
    (mapHeight : ℚ → Int) (height : ℚ)
    (rowBounds : margin < mapHeight (rationalResidue period height) ∧
      mapHeight (rationalResidue period height) < factor*period-margin)
    (vertexGap : margin < |mapHeight (rationalResidue period height)-factor*position|) :
    margin < |periodicRedistributedHeight period (factor*period) mapHeight height-
      factor*(position+period*vertexRow)| := by
  have periodPositive : 0 < period := by omega
  have outputPositive : 0 < factor*period := mul_pos factorPositive periodPositive
  have lower : 0 < factor*position := mul_pos factorPositive positionBounds.1
  have upper : factor*position < factor*period := mul_lt_mul_of_pos_left positionBounds.2 factorPositive
  unfold periodicRedistributedHeight
  rcases lt_trichotomy (rationalCell period height) vertexRow with before | same | after
  · have gap : factor*period*(rationalCell period height+1) ≤ factor*period*vertexRow := by nlinarith
    have negative : factor*period*rationalCell period height+mapHeight (rationalResidue period height)-
        factor*(position+period*vertexRow) < -margin := by nlinarith [rowBounds.2]
    rw [abs_of_neg (by omega)]
    omega
  · rw [same]
    have cancel : factor*period*vertexRow+mapHeight (rationalResidue period height)-factor*(position+period*vertexRow) =
        mapHeight (rationalResidue period height)-factor*position := by ring
    rw [cancel]
    exact vertexGap
  · have gap : factor*period*(vertexRow+1) ≤ factor*period*rationalCell period height := by nlinarith
    have positive : margin < factor*period*rationalCell period height+mapHeight (rationalResidue period height)-
        factor*(position+period*vertexRow) := by nlinarith [rowBounds.1]
    rw [abs_of_pos (by omega)]
    exact positive

end LeanTrominoes.OrthogonalDrawingRefinement
