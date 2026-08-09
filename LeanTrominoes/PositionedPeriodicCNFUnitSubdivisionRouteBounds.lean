import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Rebased route bounds under unit subdivision

The open one-period halo around a positioned incidence drawing is
orthogonally convex.  Consequently, replacing every canonical incidence
route by its ordered unit subdivision preserves the pointwise halo bound on
the corresponding reversed-and-rebased variable-to-clause routes.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Pointwise rebased-route halo bounds survive ordered unit subdivision of
every canonical incidence route. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_of_unitSubdivide
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (sourcePresentation targetPresentation :
      PlanarIncidencePresentation source placement)
    (routesEq :
      ∀ clauseIndex literalIndex,
        targetPresentation.routes clauseIndex literalIndex =
          AxisDirection.unitSubdividePolyline
            (sourcePresentation.routes clauseIndex literalIndex))
    (bounds :
      sourcePresentation.RebasedRoutePointsInExpandedSquare) :
    targetPresentation.RebasedRoutePointsInExpandedSquare := by
  intro tagged taggedMember point pointMember
  let offset :=
    placement.translation
      (Cell.sub
        (PeriodicCNF.clauseAnchor tagged.1.clause)
        tagged.1.literal.offset)
  have routeOrthogonal :=
    sourcePresentation.route_orthogonal_of_tagged taggedMember
  change
    point ∈
      PeriodicOrthocrossing.translatePolyline offset
        (targetPresentation.routes
          tagged.1.clauseIndex tagged.1.literalIndex).reverse
    at pointMember
  rw [routesEq] at pointMember
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨subdividedPoint, subdividedMember, rfl⟩
  have subdividedMember' :
      subdividedPoint ∈
        AxisDirection.unitSubdividePolyline
          (sourcePresentation.routes
            tagged.1.clauseIndex tagged.1.literalIndex) := by
    simpa using subdividedMember
  have sourcePointInside :
      ∀ sourcePoint ∈
          sourcePresentation.routes
            tagged.1.clauseIndex tagged.1.literalIndex,
        (incidenceDrawing source placement sourcePresentation.routes)
          |>.PositionInExpandedSquare (Cell.add offset sourcePoint) := by
    intro sourcePoint sourcePointMember
    apply bounds tagged taggedMember
    change
      Cell.add offset sourcePoint ∈
        PeriodicOrthocrossing.translatePolyline offset
          (sourcePresentation.routes
            tagged.1.clauseIndex tagged.1.literalIndex).reverse
    unfold PeriodicOrthocrossing.translatePolyline
    exact List.mem_map.mpr
      ⟨sourcePoint, by simpa using sourcePointMember, rfl⟩
  have transferDrawingBounds {boundedPoint : Cell}
      (inside :
        (incidenceDrawing source placement sourcePresentation.routes)
          |>.PositionInExpandedSquare boundedPoint) :
      (incidenceDrawing source placement targetPresentation.routes)
        |>.PositionInExpandedSquare boundedPoint := by
    simpa only [PeriodicGridDrawing.PositionInExpandedSquare,
      incidenceDrawing_gridSize source placement
        sourcePresentation.routes sourcePresentation.periodPositive,
      incidenceDrawing_gridSize source placement
        targetPresentation.routes targetPresentation.periodPositive]
      using inside
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        routeOrthogonal subdividedMember' with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact transferDrawingBounds
      (sourcePointInside subdividedPoint originalMember)
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    let translatedSegment := segment.translate offset
    have translatedContains :
        translatedSegment.Contains
          (Cell.add offset subdividedPoint) := by
      simpa [translatedSegment, GridSegment.translate, Cell.add, add_comm] using
        (PeriodicGridDrawing.contains_translate_iff
          segment offset subdividedPoint).2
            (GridSegment.contains_of_interiorContains interior)
    exact PeriodicGridDrawing.expanded_of_contains
      (by
        simpa [translatedSegment, GridSegment.translate] using
          transferDrawingBounds
            (sourcePointInside segment.start endpoints.1))
      (by
        simpa [translatedSegment, GridSegment.translate] using
          transferDrawingBounds
            (sourcePointInside segment.finish endpoints.2))
      translatedContains

end PositionedPeriodicCNF
end LeanTrominoes
