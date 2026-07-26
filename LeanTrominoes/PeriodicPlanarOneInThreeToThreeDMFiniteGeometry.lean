import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexDistinctness
import LeanTrominoes.PeriodicGridDrawingFinitePlanarity

/-!
# Finite planarity certificates for the assembled 3DM drawing

The assembled periodic drawing has finitely many stored vertices and route
segments, but its planarity predicate quantifies over all periodic translates.
Once all stored segment endpoints lie in the open fundamental square, the
general neighboring-translate checker reduces those global obligations to two
Boolean equalities.

This file packages precisely that remaining executable certificate.  For the
standard normalized construction, the already proved vertex distinctness and
fundamental-square bounds fill the other two fields of `AssemblyGeometry`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Finite data sufficient to prove global planarity of an assembled periodic
3DM drawing. -/
structure FiniteAssemblyPlanarityCertificate
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : Prop where
  endpointBounds :
    (assembledDrawing routing).SegmentEndpointsInFundamentalSquare
  routesChecked :
    (assembledDrawing routing).finiteRoutesAvoidInteriors = true
  verticesChecked :
    (assembledDrawing routing).finiteVerticesAvoidRouteInteriors = true

namespace FiniteAssemblyPlanarityCertificate

/-- The finite neighboring-translate checks imply planarity of the complete
infinite periodic lift. -/
theorem planar
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (certificate : FiniteAssemblyPlanarityCertificate routing)
    (positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position) :
    (assembledDrawing routing).IsPlanar := by
  exact PeriodicGridDrawing.isPlanar_of_finite
    certificate.endpointBounds positionsInside
    certificate.routesChecked certificate.verticesChecked

/-- Add the two previously isolated vertex obligations to obtain the complete
global assembly geometry certificate. -/
def toAssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (certificate : FiniteAssemblyPlanarityCertificate routing)
    (positionsNodup : (assembledVertexPositions routing).Nodup)
    (positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position) :
    AssemblyGeometry routing where
  positionsNodup := positionsNodup
  positionsInside := positionsInside
  planar := certificate.planar positionsInside

end FiniteAssemblyPlanarityCertificate

/-- For the normalized reduction source, a finite route certificate is the
only remaining input needed for the complete assembled geometry. -/
def standardNormalizedAssemblyGeometryOfFinite
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (certificate :
      FiniteAssemblyPlanarityCertificate
        (constructedThreeStrandRouting
          (normalizedIncidencePresentation presentation)
          standardThreeStrandLayout)) :
    AssemblyGeometry
      (constructedThreeStrandRouting
        (normalizedIncidencePresentation presentation)
        standardThreeStrandLayout) :=
  certificate.toAssemblyGeometry
    (standardNormalizedAssembledVertexPositions_nodup presentation)
    (standardNormalizedAssembledVertexPositions_inside presentation)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
