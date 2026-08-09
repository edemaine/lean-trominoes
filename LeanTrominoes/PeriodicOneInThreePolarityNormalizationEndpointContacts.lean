import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRawLiftedSeparation
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing

/-!
# Endpoint contacts after polarity-normalization gauging

The final fresh-variable gauge only changes canonical representatives of
the raw split routes by whole-period translations.  Relative route
separation and route-local simplicity therefore pass to the final
polarity-normalized drawing, yielding its ribbon-readiness certificate.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Complete raw lifted separation can be reindexed by raw positioned
incidences. -/
theorem rawRelativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes) := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  have rawRelative :
      (rawIncidenceDrawing continuous)
        |>.RelativeLiftedRoutesAvoidEachOther :=
    (PeriodicGridDrawing.liftedRoutesAvoidEachOther_iff_relative
      (rawIncidenceDrawing continuous)).mp
        (rawIncidenceDrawing_liftedRoutesAvoidEachOther
          presentation sourceUnitSteps)
  exact
    PositionedPeriodicCNF.relativeIncidenceRoutesAvoidEachOther_of_incidenceDrawing
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawPlacement_periodPositive continuous)
      (by simpa [rawIncidenceDrawing] using rawRelative)

/-- Relative incidence-route separation survives the final fresh-variable
gauge. -/
theorem incidenceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes) := by
  simpa [formula, placement, incidenceRoutes] using
    (rawRelativeIncidenceRoutesAvoidEachOther
      presentation sourceUnitSteps).variableGaugeCanonicalIncidenceRoutes
        freshGauge

/-- The final anonymous route list satisfies complete relative lifted-route
separation. -/
theorem incidenceDrawing_relativeLiftedRoutesAvoidEachOther
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
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.RelativeLiftedRoutesAvoidEachOther := by
  have periodPositive :
      0 < (placement sourcePlacement presentation.routes).period := by
    rw [placement_period_eq_refinedPlacement_period]
    exact
      (scaledSourcePresentation
        presentation.toContinuousPlanarIncidencePresentation).periodPositive
  exact PositionedPeriodicCNF.incidenceDrawing_relativeLiftedRoutesAvoidEachOther
    (formula source sourcePlacement presentation.routes)
    (placement sourcePlacement presentation.routes)
    (incidenceRoutes source sourcePlacement presentation.routes)
    periodPositive
    (incidenceRoutes_relativeAvoidEachOther presentation sourceUnitSteps)

/-- Every final gauged polarity-normalized route is simple. -/
theorem incidenceDrawing_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement) :
    ∀ route ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (formula source sourcePlacement presentation.routes)
          (placement sourcePlacement presentation.routes)
          (incidenceRoutes source sourcePlacement presentation.routes))
          |>.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  simpa [formula, placement, incidenceRoutes, rawIncidenceDrawing] using
    PositionedPeriodicCNF.routesSimple_variableGaugeCanonicalIncidenceRoutes
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawIncidenceDrawing_routesSimple presentation)

/-- The final polarity-normalized drawing has endpoint-only listed-point
contacts. -/
theorem incidenceDrawing_routePointsMeetOnlyAtEndpoints
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
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.RoutePointsMeetOnlyAtEndpoints := by
  let drawing := PositionedPeriodicCNF.incidenceDrawing
    (formula source sourcePlacement presentation.routes)
    (placement sourcePlacement presentation.routes)
    (incidenceRoutes source sourcePlacement presentation.routes)
  exact
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
      ((PeriodicGridDrawing.liftedRoutesAvoidEachOther_iff_relative
        drawing).mpr
          (incidenceDrawing_relativeLiftedRoutesAvoidEachOther
            presentation sourceUnitSteps))
      (incidenceDrawing_routesSimple presentation)

/-- The final polarity-normalized drawing has the complete geometric
ribbon-readiness certificate. -/
theorem incidenceDrawing_isRibbonReady
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
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    (incidenceDrawing_relativeLiftedRoutesAvoidEachOther
      presentation sourceUnitSteps)
    (incidenceDrawing_routesSimple presentation)
    (incidenceDrawing_hasUnitSteps
      presentation.toContinuousPlanarIncidencePresentation)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
