import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexDistinctness
import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity
import LeanTrominoes.PeriodicContinuousPlanarThreeDM

/-!
# Finite planarity certificates for the assembled 3DM drawing

The assembled periodic drawing has finitely many stored vertices and route
segments, but its planarity predicate quantifies over all periodic translates.
Once all stored segment endpoints lie in the open one-cell halo around the
fundamental square, the expanded neighboring-translate checker reduces those
global obligations to two Boolean equalities.

This file packages precisely that remaining executable certificate.  For the
standard normalized construction, the already proved vertex distinctness and
fundamental-square bounds fill the other two fields of `AssemblyGeometry`.

The continuous refinement adds the collinear-interior check needed before
contracting degree-two vertices or rasterizing the drawing.  In particular,
it rules out the coincident unit segments that the integer-point definition
of planarity intentionally cannot detect.
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
    (assembledDrawing routing).SegmentEndpointsInExpandedSquare
  routesChecked :
    (assembledDrawing routing).expandedFiniteRoutesAvoidInteriors = true
  verticesChecked :
    (assembledDrawing routing).finiteVerticesAvoidRouteInteriors = true

/-- The additional finite check needed for exact continuous separation of
distinct route-segment occurrences. -/
structure FiniteContinuousAssemblyPlanarityCertificate
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : Prop
    extends FiniteAssemblyPlanarityCertificate routing where
  continuousChecked :
    (assembledDrawing routing).expandedFiniteRoutesHaveDisjointInteriors =
      true

/-- Global geometry strong enough for subsequent degree-two contraction and
geometric normalization. -/
structure ContinuousAssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : Prop where
  positionsNodup :
    (assembledVertexPositions routing).Nodup
  positionsInside :
    ∀ position ∈ assembledVertexPositions routing,
      (assembledDrawing routing).PositionInFundamentalSquare position
  continuouslyPlanar :
    (assembledDrawing routing).IsContinuouslyPlanar

namespace ContinuousAssemblyGeometry

/-- Forgetting continuous segment separation recovers the basic assembly
geometry consumed by the existing planar-presentation interface. -/
def toAssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (geometry : ContinuousAssemblyGeometry routing) :
    AssemblyGeometry routing where
  positionsNodup := geometry.positionsNodup
  positionsInside := geometry.positionsInside
  planar := geometry.continuouslyPlanar.isPlanar

/-- Package continuously planar assembly geometry as the stronger periodic
3DM presentation used by the contraction layer. -/
def toContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (geometry : ContinuousAssemblyGeometry routing) :
    (encodedProblem source).ContinuousPlanarPresentation where
  toPlanarPresentation :=
    assembledPlanarPresentation routing geometry.toAssemblyGeometry
  continuouslyPlanar := geometry.continuouslyPlanar

end ContinuousAssemblyGeometry

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
  exact PeriodicGridDrawing.isPlanar_of_expandedFinite
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

namespace FiniteContinuousAssemblyPlanarityCertificate

/-- The three neighboring-translate checks prove exact continuous planarity
of the full periodic lift. -/
theorem continuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (certificate : FiniteContinuousAssemblyPlanarityCertificate routing)
    (positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position) :
    (assembledDrawing routing).IsContinuouslyPlanar := by
  exact PeriodicGridDrawing.isContinuouslyPlanar_of_expandedFinite
    certificate.endpointBounds positionsInside
    certificate.routesChecked certificate.verticesChecked
    certificate.continuousChecked

/-- Add the established vertex obligations to a finite continuous route
certificate. -/
def toContinuousAssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routing : ThreeStrandRouting source}
    (certificate : FiniteContinuousAssemblyPlanarityCertificate routing)
    (positionsNodup : (assembledVertexPositions routing).Nodup)
    (positionsInside :
      ∀ position ∈ assembledVertexPositions routing,
        (assembledDrawing routing).PositionInFundamentalSquare position) :
    ContinuousAssemblyGeometry routing where
  positionsNodup := positionsNodup
  positionsInside := positionsInside
  continuouslyPlanar := certificate.continuouslyPlanar positionsInside

end FiniteContinuousAssemblyPlanarityCertificate

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

/-- Continuous version of `standardNormalizedAssemblyGeometryOfFinite`.
Only the three finite route checks remain after the normalized vertex
theorems are supplied. -/
def standardNormalizedContinuousAssemblyGeometryOfFinite
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (certificate :
      FiniteContinuousAssemblyPlanarityCertificate
        (constructedThreeStrandRouting
          (normalizedIncidencePresentation presentation)
          standardThreeStrandLayout)) :
    ContinuousAssemblyGeometry
      (constructedThreeStrandRouting
        (normalizedIncidencePresentation presentation)
        standardThreeStrandLayout) :=
  certificate.toContinuousAssemblyGeometry
    (standardNormalizedAssembledVertexPositions_nodup presentation)
    (standardNormalizedAssembledVertexPositions_inside presentation)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
