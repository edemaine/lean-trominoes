import LeanTrominoes.PeriodicGridDrawingFiniteContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Finite certificates for positioned periodic incidence drawings

For route and vertex coordinates contained in one open fundamental square,
all possible contacts in the infinite periodic lift reduce to comparisons
against the nine neighboring translates.  This file packages those finite
checks with endpoint compatibility and orthogonality.

An explicit drawing construction can therefore establish a continuously
planar incidence presentation by proving finite coordinate bounds and three
Boolean equalities.  The conversion below handles all graph-list and
infinite-period bookkeeping.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Complete finite data needed to certify a continuously planar positioned
periodic CNF incidence drawing. -/
structure FiniteContinuousPlanarIncidenceCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) where
  routes : IncidenceRoutes
  periodPositive : 0 < placement.period
  positionsNodup :
    (incidenceVertexPositions source placement).Nodup
  vertexBounds :
    ∀ position ∈ incidenceVertexPositions source placement,
      (incidenceDrawing source placement routes).PositionInFundamentalSquare
        position
  endpointBounds :
    (incidenceDrawing source placement routes).SegmentEndpointsInFundamentalSquare
  routesMatch :
    (incidenceDrawing source placement routes).RoutesMatch
      source.erase.incidenceGraph
  orthogonal :
    (incidenceDrawing source placement routes).IsOrthogonal
  routesChecked :
    (incidenceDrawing source placement routes).finiteRoutesAvoidInteriors = true
  verticesChecked :
    (incidenceDrawing source placement routes).finiteVerticesAvoidRouteInteriors = true
  continuousChecked :
    (incidenceDrawing source placement routes).finiteRoutesHaveDisjointInteriors = true

namespace FiniteContinuousPlanarIncidenceCertificate

/-- The elementary certificate fields supply complete graph compatibility. -/
theorem isCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      FiniteContinuousPlanarIncidenceCertificate source placement) :
    (incidenceDrawing source placement
      certificate.routes).IsCompatible
        source.erase.incidenceGraph := by
  exact
    ⟨PeriodicCNF.incidenceGraph_isWellFormed source.erase,
      incidenceVertexPositions_length source placement,
      incidenceEdgeRoutes_length source certificate.routes,
      certificate.positionsNodup,
      certificate.vertexBounds,
      certificate.routesMatch⟩

/-- The three finite neighboring-translate checks imply exact continuous
planarity of the infinite periodic lift. -/
theorem isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      FiniteContinuousPlanarIncidenceCertificate source placement) :
    (incidenceDrawing source placement
      certificate.routes).IsContinuouslyPlanar := by
  exact
    PeriodicGridDrawing.isContinuouslyPlanar_of_finite
      certificate.endpointBounds certificate.vertexBounds
      certificate.routesChecked certificate.verticesChecked
      certificate.continuousChecked

/-- Promote a finite certificate to the geometric interface consumed by the
planar exact-one-to-3DM assembly. -/
def toContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      FiniteContinuousPlanarIncidenceCertificate source placement) :
    ContinuousPlanarIncidencePresentation source placement where
  routes := certificate.routes
  periodPositive := certificate.periodPositive
  compatible := certificate.isCompatible
  orthogonal := certificate.orthogonal
  planar := certificate.isContinuouslyPlanar.isPlanar
  continuouslyPlanar := certificate.isContinuouslyPlanar

end FiniteContinuousPlanarIncidenceCertificate
end PositionedPeriodicCNF
end LeanTrominoes
