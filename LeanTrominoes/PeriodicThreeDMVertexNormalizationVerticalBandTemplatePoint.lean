/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedRayRasterizationCorridor
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandPosition

/-!
# Vertical-band bounds for local normalization-template points
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicThreeDM

/-- Every point within radius three of the affine image of an old band point
lies in the enlarged open vertical halo. -/
theorem withinThree_normalizeVertexPosition_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing} {position point : Cell}
    (positionInside :
      drawing.PositionInExpandedVerticalBand position)
    (near :
      WithinCoordinateRadius 3
        (normalizeVertexPosition position) point) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PositionInExpandedVerticalBand point := by
  simp only [PeriodicGridDrawing.PositionInExpandedVerticalBand]
    at positionInside ⊢
  rw [vertexNormalizationMagnifiedUnitDrawing_gridSize]
  simp only [WithinCoordinateRadius] at near
  have verticalAbsolute :
      |point.2 - (normalizeVertexPosition position).2| ≤ (3 : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast near.2
  have verticalBounds := abs_le.mp verticalAbsolute
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add]
    at verticalBounds
  have gridPositive : 0 < drawing.gridSize :=
    Nat.zero_lt_succ drawing.gridSizePred
  norm_num at positionInside verticalBounds ⊢
  constructor <;> omega

end PeriodicThreeDM
end LeanTrominoes
