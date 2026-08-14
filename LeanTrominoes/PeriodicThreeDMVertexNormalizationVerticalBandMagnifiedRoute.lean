/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBandConvex
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandPosition

/-!
# Vertical-band bounds for magnified normalization routes
-/

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Magnification, affine translation, and ordered unit subdivision preserve
pointwise vertical-band membership for an orthogonal polyline. -/
theorem magnifiedUnitRoute_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing} {route : List Cell}
    (orthogonal : OrthogonalPolyline route)
    (inside : drawing.PolylineInExpandedVerticalBand route) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInExpandedVerticalBand
        (magnifiedUnitRoute route) := by
  intro point pointMember
  have mappedOrthogonal :
      OrthogonalPolyline (route.map normalizeVertexPosition) := by
    rw [map_normalizeVertexPosition_eq_translate_scalePolyline_for_band]
    have scaled :
        OrthogonalPolyline
          (scalePolyline vertexNormalizationScale route) := by
      simpa [vertexNormalizationScale] using
        OrthogonalPolyline.scalePolyline orthogonal
          (factor := 12) (by norm_num)
    exact scaled.translate center
  unfold magnifiedUnitRoute at pointMember
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        mappedOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · rcases List.mem_map.mp originalMember with
      ⟨source, sourceMember, rfl⟩
    exact normalizeVertexPosition_inExpandedVerticalBand
      (inside source sourceMember)
  · have endpointMembers :=
      gridPolylineSegments_endpoints_mem segmentMember
    rcases List.mem_map.mp endpointMembers.1 with
      ⟨sourceStart, sourceStartMember, startEq⟩
    rcases List.mem_map.mp endpointMembers.2 with
      ⟨sourceFinish, sourceFinishMember, finishEq⟩
    apply
      PeriodicGridDrawing.PositionInExpandedVerticalBand.of_segment_contains
    · rw [← startEq]
      exact normalizeVertexPosition_inExpandedVerticalBand
        (inside sourceStart sourceStartMember)
    · rw [← finishEq]
      exact normalizeVertexPosition_inExpandedVerticalBand
        (inside sourceFinish sourceFinishMember)
    · exact GridSegment.contains_of_interiorContains interior

end PeriodicThreeDM
end LeanTrominoes
