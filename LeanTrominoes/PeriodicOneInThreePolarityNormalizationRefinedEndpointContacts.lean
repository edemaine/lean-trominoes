import LeanTrominoes.PeriodicGridDrawingRibbonScalingSeparation
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionRibbon
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFRibbonRouteFamily

/-!
# Endpoint contacts in the refined polarity-normalization source

Before an incompatible incidence is split into three routes, the source
drawing is anchor-normalized, scaled by three, and unit-subdivided.  Positive
scaling and ordered subdivision preserve complete lifted separation, so the
resulting refined route family still has only advertised endpoint contacts.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The scaled source drawing is literally the threefold scale of the
original source drawing; anchor normalization changes no finite geometry. -/
theorem scaledSource_incidenceDrawing_eq_scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (scaledSourcePresentation presentation).routes =
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).scale
          refinementFactor := by
  change
    PositionedPeriodicCNF.incidenceDrawing
        ((source.anchorNormalize sourcePlacement).scale refinementFactor)
        (sourcePlacement.scale refinementFactor)
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          refinementFactor presentation.routes) =
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).scale
          refinementFactor
  rw [PositionedPeriodicCNF.incidenceDrawing_scale
    refinementFactor (source.anchorNormalize sourcePlacement)
    sourcePlacement presentation.routes presentation.periodPositive]
  rw [PositionedPeriodicCNF.incidenceDrawing_anchorNormalize]

/-- The complete refined route family is the unit subdivision of the
threefold-scaled source drawing. -/
theorem refinedIncidenceDrawing_eq_scaled_unitSubdivide
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (refinedRouteFamily presentation).routes =
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (scaledSourcePresentation presentation).routes).unitSubdivide := by
  unfold PositionedPeriodicCNF.incidenceDrawing
    PeriodicGridDrawing.unitSubdivide
  congr 1
  change
    PositionedPeriodicCNF.incidenceEdgeRoutes
        (refinedSource source sourcePlacement)
        (refinedRouteFamily presentation).routes =
      (PositionedPeriodicCNF.incidenceEdgeRoutes
        (refinedSource source sourcePlacement)
        (scaledSourcePresentation presentation).routes).map
          AxisDirection.unitSubdividePolyline
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
    PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
    List.map_map]
  apply List.map_congr_left
  intro incidence incidenceMember
  rfl

/-- The scaled source drawing inherits complete lifted separation from a
ribbon-ready unit-step source presentation. -/
theorem scaledSource_liftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    (PositionedPeriodicCNF.incidenceDrawing
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation
        presentation.toContinuousPlanarIncidencePresentation).routes)
        |>.LiftedRoutesAvoidEachOther := by
  let sourceDrawing := PositionedPeriodicCNF.incidenceDrawing
    source sourcePlacement presentation.routes
  have sourceRelative :
      sourceDrawing.RelativeLiftedRoutesAvoidEachOther :=
    PeriodicGridDrawing.relativeLiftedRoutesAvoidEachOther_of_isRibbonReady_of_hasUnitSteps
      ⟨presentation.continuouslyPlanar, presentation.endpointContacts⟩
      sourceUnitSteps
      presentation.toPlanarIncidencePresentation.routes_length_ge_two
  have sourceLifted : sourceDrawing.LiftedRoutesAvoidEachOther :=
    (PeriodicGridDrawing.liftedRoutesAvoidEachOther_iff_relative
      sourceDrawing).mpr sourceRelative
  rw [scaledSource_incidenceDrawing_eq_scale
    presentation.toContinuousPlanarIncidencePresentation]
  exact PeriodicGridDrawing.liftedRoutesAvoidEachOther_scale
    refinementFactor_positive sourceDrawing sourceLifted

/-- The refined source route family has no listed-point contacts except at
the outer endpoints of both complete refined routes. -/
theorem refinedRouteFamily_routePointsMeetOnlyAtEndpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    (PositionedPeriodicCNF.incidenceDrawing
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (refinedRouteFamily
        presentation.toContinuousPlanarIncidencePresentation).routes)
        |>.RoutePointsMeetOnlyAtEndpoints := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  let scaled := scaledSourcePresentation continuous
  let scaledDrawing := PositionedPeriodicCNF.incidenceDrawing
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement) scaled.routes
  have scaledSeparated : scaledDrawing.LiftedRoutesAvoidEachOther :=
    scaledSource_liftedRoutesAvoidEachOther presentation sourceUnitSteps
  have scaledOrthogonal : scaledDrawing.IsOrthogonal := scaled.orthogonal
  have scaledLengths : ∀ route ∈ scaledDrawing.edgeRoutes,
      2 ≤ route.length :=
    scaled.toPlanarIncidencePresentation.routes_length_ge_two
  have scaledNonempty : ∀ route ∈ scaledDrawing.edgeRoutes,
      route ≠ [] := by
    intro route routeMember routeEmpty
    have length := scaledLengths route routeMember
    rw [routeEmpty] at length
    simp at length
  have sourceSimple :
      ∀ route ∈
          (PositionedPeriodicCNF.incidenceDrawing
            source sourcePlacement presentation.routes).edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route :=
    presentation.routesSimple
  have scaledSimple : ∀ route ∈ scaledDrawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
    have scaledDrawingEqual :
        scaledDrawing =
          (PositionedPeriodicCNF.incidenceDrawing
            source sourcePlacement presentation.routes).scale
              refinementFactor :=
      scaledSource_incidenceDrawing_eq_scale continuous
    rw [scaledDrawingEqual]
    exact PeriodicGridDrawing.routesSimple_scale
      refinementFactor_positive _ sourceSimple
  rw [refinedIncidenceDrawing_eq_scaled_unitSubdivide continuous]
  exact
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_unitSubdivide
      scaledDrawing scaledSeparated scaledOrthogonal
      scaledNonempty scaledSimple

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
