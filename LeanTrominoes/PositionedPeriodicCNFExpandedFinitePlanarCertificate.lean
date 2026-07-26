import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Halo-bounded finite certificates for positioned periodic CNF drawings

The original finite certificate requires every stored route endpoint to lie
inside the canonical fundamental square.  That is suitable for zero-offset
local fixtures, but a genuine nonzero-offset periodic incidence ends in a
neighboring square.

This certificate uses the open one-cell halo and the complete 25-translation
route checks.  It therefore packages the continuously planar positioned
incidence presentations needed by the periodic hardness construction without
excluding boundary-crossing graph edges.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Complete finite data for a continuously planar positioned periodic CNF
drawing whose stored route endpoints may enter a neighboring square. -/
structure ExpandedFiniteContinuousPlanarIncidenceCertificate
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
    (incidenceDrawing source placement routes)
      |>.SegmentEndpointsInExpandedSquare
  routesMatch :
    (incidenceDrawing source placement routes).RoutesMatch
      source.erase.incidenceGraph
  orthogonal :
    (incidenceDrawing source placement routes).IsOrthogonal
  routesChecked :
    (incidenceDrawing source placement routes
      |>.expandedFiniteRoutesAvoidInteriors) = true
  verticesChecked :
    (incidenceDrawing source placement routes
      |>.finiteVerticesAvoidRouteInteriors) = true
  continuousChecked :
    (incidenceDrawing source placement routes
      |>.expandedFiniteRoutesHaveDisjointInteriors) = true

namespace ExpandedFiniteContinuousPlanarIncidenceCertificate

/-- The elementary certificate fields give complete graph compatibility. -/
theorem isCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      ExpandedFiniteContinuousPlanarIncidenceCertificate
        source placement) :
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

/-- The expanded finite checks prove exact continuous planarity of the
infinite periodic lift. -/
theorem isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      ExpandedFiniteContinuousPlanarIncidenceCertificate
        source placement) :
    (incidenceDrawing source placement
      certificate.routes).IsContinuouslyPlanar := by
  exact
    PeriodicGridDrawing.isContinuouslyPlanar_of_expandedFinite
      certificate.endpointBounds certificate.vertexBounds
      certificate.routesChecked certificate.verticesChecked
      certificate.continuousChecked

/-- Promote the halo-bounded finite certificate to the geometric interface
consumed by the exact-one-to-3DM assembly. -/
def toContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      ExpandedFiniteContinuousPlanarIncidenceCertificate
        source placement) :
    ContinuousPlanarIncidencePresentation source placement where
  routes := certificate.routes
  periodPositive := certificate.periodPositive
  compatible := certificate.isCompatible
  orthogonal := certificate.orthogonal
  planar := certificate.isContinuouslyPlanar.isPlanar
  continuouslyPlanar := certificate.isContinuouslyPlanar

/-- Promote a finite drawing certificate together with the one additional
rebased-route halo bound needed by the planar 3DM assembly. -/
def toHaloBoundedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (certificate :
      ExpandedFiniteContinuousPlanarIncidenceCertificate
        source placement)
    (rebasedRoutePointsInside :
      certificate.toContinuousPlanarIncidencePresentation
        |>.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquare) :
    HaloBoundedContinuousPlanarIncidencePresentation
      source placement where
  toContinuousPlanarIncidencePresentation :=
    certificate.toContinuousPlanarIncidencePresentation
  rebasedRoutePointsInside := rebasedRoutePointsInside

end ExpandedFiniteContinuousPlanarIncidenceCertificate
end PositionedPeriodicCNF
end LeanTrominoes
