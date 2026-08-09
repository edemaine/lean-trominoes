import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteContinuousPlanarityTransfer
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeContinuousPlanarity

/-!
# A continuously planar polarity-normalized presentation

The raw split routes inherit exact continuous separation from the refined
source drawing.  Variable-gauge transport then supplies the same separation
for the final polarity-normalized drawing, completing its packaged planar
incidence presentation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The final fresh-variable gauge preserves continuous relative-interior
separation of every pair of distinct periodic segment occurrences. -/
theorem incidenceDrawing_routesHaveDisjointInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.RoutesHaveDisjointInteriors := by
  simpa [formula, placement, incidenceRoutes, rawIncidenceDrawing] using
    PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesHaveDisjointInteriors
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawPlacement_periodPositive presentation)
      (rawIncidenceDrawing_isContinuouslyPlanar presentation)

/-- The final polarity-normalized incidence drawing is continuously planar. -/
theorem incidenceDrawing_isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.IsContinuouslyPlanar :=
  ⟨incidenceDrawing_isPlanar presentation,
    incidenceDrawing_routesHaveDisjointInteriors presentation⟩

/-- Polarity normalization transports any continuously planar positioned
incidence presentation to one for the normalized formula. -/
def continuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes) where
  routes := incidenceRoutes source sourcePlacement presentation.routes
  periodPositive := by
    rw [placement_period_eq_refinedPlacement_period]
    exact (scaledSourcePresentation presentation).periodPositive
  compatible := incidenceDrawing_isCompatible presentation
  orthogonal := incidenceDrawing_isOrthogonal presentation
  planar := incidenceDrawing_isPlanar presentation
  continuouslyPlanar := incidenceDrawing_isContinuouslyPlanar presentation

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
