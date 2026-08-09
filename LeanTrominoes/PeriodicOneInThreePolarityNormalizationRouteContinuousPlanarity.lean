import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionContinuousPlanarity
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteCompatibility

/-!
# Continuous planarity of polarity-normalized route subdivision

This module transports continuous planarity through the geometric route
operations used by positioned polarity normalization.  The refined source
drawing is handled first; its routes are precisely the ordered unit
subdivisions of the threefold-scaled source routes.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The complete refined source route family is still continuously planar. -/
theorem refinedRouteFamily_isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (refinedRouteFamily presentation).routes)
        |>.IsContinuouslyPlanar := by
  let scaled := scaledSourcePresentation presentation
  have drawingEqual :
      PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (refinedRouteFamily presentation).routes =
        (PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          scaled.routes).unitSubdivide := by
    unfold PositionedPeriodicCNF.incidenceDrawing
      PeriodicGridDrawing.unitSubdivide
    congr 1
    change
      PositionedPeriodicCNF.incidenceEdgeRoutes
          (refinedSource source sourcePlacement)
          (refinedRouteFamily presentation).routes =
        (PositionedPeriodicCNF.incidenceEdgeRoutes
          (refinedSource source sourcePlacement)
          scaled.routes).map
            AxisDirection.unitSubdividePolyline
    rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
      PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
      List.map_map]
    apply List.map_congr_left
    intro incidence incidenceMember
    rfl
  rw [drawingEqual]
  exact
    PeriodicGridDrawing.isContinuouslyPlanar_unitSubdivide
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        scaled.routes)
      scaled.continuouslyPlanar scaled.orthogonal

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
