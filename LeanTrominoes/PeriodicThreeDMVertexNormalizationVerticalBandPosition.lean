/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBand
import LeanTrominoes.PeriodicThreeDMVertexNormalizationMagnifiedContacts

/-!
# Vertical-band bounds for normalized vertex positions
-/

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Mapping the normalization affine map over a route is scaling followed by
translation by the template center. -/
theorem map_normalizeVertexPosition_eq_translate_scalePolyline_for_band
    (points : List Cell) :
    points.map normalizeVertexPosition =
      translatePolyline center
        (scalePolyline vertexNormalizationScale points) := by
  induction points with
  | nil => rfl
  | cons point rest induction =>
      simp only [List.map_cons, scalePolyline_cons,
        translatePolyline, induction]
      rw [show normalizeVertexPosition point =
          Cell.add center
            (Cell.scale vertexNormalizationScale point) by
        simp [normalizeVertexPosition, Cell.add, add_comm]]

/-- The affine image of one old band point lies in the enlarged band's
interior. -/
theorem normalizeVertexPosition_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInExpandedVerticalBand position) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PositionInExpandedVerticalBand
        (normalizeVertexPosition position) := by
  simp only [PeriodicGridDrawing.PositionInExpandedVerticalBand]
    at inside ⊢
  rw [vertexNormalizationMagnifiedUnitDrawing_gridSize]
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add]
  have gridPositive : 0 < drawing.gridSize :=
    Nat.zero_lt_succ drawing.gridSizePred
  norm_num at inside ⊢
  constructor <;> omega

end PeriodicThreeDM
end LeanTrominoes
