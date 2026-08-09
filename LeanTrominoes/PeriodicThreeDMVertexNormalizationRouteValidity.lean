import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.PeriodicThreeDMNormalizationRouteRasterization

/-!
# Validity of degree-three normalization routes

The rasterizer expects every normalized edge route to consist of unit axis
steps without immediate reversals.  This module establishes those invariants
from the continuous planar presentation.  The first layer below isolates the
generic affine magnification, unit subdivision, and endpoint trimming shared
by all three normalization rounds.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Mapping the normalization affine map is scaling followed by translation
by the template center. -/
theorem map_normalizeVertexPosition_eq_translate_scalePolyline
    (points : List Cell) :
    points.map normalizeVertexPosition =
      PeriodicOrthocrossing.translatePolyline center
        (scalePolyline vertexNormalizationScale points) := by
  induction points with
  | nil => rfl
  | cons point rest induction =>
      simp only [List.map_cons, scalePolyline_cons,
        PeriodicOrthocrossing.translatePolyline, induction]
      rw [show normalizeVertexPosition point =
          Cell.add center (Cell.scale vertexNormalizationScale point) by
        simp [normalizeVertexPosition, Cell.add_comm]]

/-- Affine magnification and ordered unit subdivision preserve
orthogonality. -/
theorem magnifiedUnitRoute_orthogonal
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (magnifiedUnitRoute points) := by
  unfold magnifiedUnitRoute
  rw [map_normalizeVertexPosition_eq_translate_scalePolyline]
  apply AxisDirection.unitSubdividePolyline_orthogonal
  have scaled : PeriodicOrthocrossing.OrthogonalPolyline
      (scalePolyline vertexNormalizationScale points) := by
    simpa [vertexNormalizationScale] using
      PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
        orthogonal (factor := 12) (by norm_num)
  exact scaled.translate center

/-- Every magnified and subdivided orthogonal route consists of unit axis
steps. -/
theorem magnifiedUnitRoute_unitSteps
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (magnifiedUnitRoute points).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold magnifiedUnitRoute
  rw [map_normalizeVertexPosition_eq_translate_scalePolyline]
  apply AxisDirection.unitSubdividePolyline_unitSteps
  have scaled : PeriodicOrthocrossing.OrthogonalPolyline
      (scalePolyline vertexNormalizationScale points) := by
    simpa [vertexNormalizationScale] using
      PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
        orthogonal (factor := 12) (by norm_num)
  exact scaled.translate center

/-- Dropping and taking the endpoint clearance margins preserves the
unit-step chain. -/
theorem trimmedMagnifiedRoute_unitSteps
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (trimmedMagnifiedRoute points).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold trimmedMagnifiedRoute
  exact ((magnifiedUnitRoute_unitSteps orthogonal).drop 3).take _

/-- The trimmed middle is consequently still an orthogonal polyline. -/
theorem trimmedMagnifiedRoute_orthogonal
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (trimmedMagnifiedRoute points) := by
  exact (trimmedMagnifiedRoute_unitSteps orthogonal).imp
    fun _ _ step => step.isAxisAligned

end PeriodicThreeDM
end LeanTrominoes
