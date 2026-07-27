import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMFiniteGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouting

/-!
# Finite geometry interface for corrected ribbon routing

The corrected ribbon construction changes the three colored incidence
corridors but retains the standard normalized period and all variable- and
clause-gadget origins.  Consequently the existing vertex distinctness and
fundamental-square bounds transfer definitionally to the corrected routing.

This leaves only the route-specific finite continuous-planarity certificate
before the corrected assembly can be packaged as global continuous geometry.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- The assembled gadget vertices remain pairwise distinct when the old
temporary incidence routes are replaced by corrected ribbon routes. -/
theorem normalizedRibbonAssembledVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    (assembledVertexPositions
      (normalizedRibbonThreeStrandRouting presentation)).Nodup := by
  change
    (assembledVertexPositions
      (standardNormalizedThreeStrandRouting
        presentation.toHaloBoundedContinuousPlanarIncidencePresentation)).Nodup
  exact
    standardNormalizedAssembledVertexPositions_nodup
      presentation.toPlanarIncidencePresentation

/-- Every assembled gadget vertex remains in the normalized fundamental
square for the corrected routing. -/
theorem normalizedRibbonAssembledVertexPositions_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    ∀ position ∈
        assembledVertexPositions
          (normalizedRibbonThreeStrandRouting presentation),
      (assembledDrawing
        (normalizedRibbonThreeStrandRouting presentation))
        |>.PositionInFundamentalSquare position := by
  change
    ∀ position ∈
        assembledVertexPositions
          (standardNormalizedThreeStrandRouting
            presentation.toHaloBoundedContinuousPlanarIncidencePresentation),
      (assembledDrawing
        (standardNormalizedThreeStrandRouting
          presentation.toHaloBoundedContinuousPlanarIncidencePresentation))
        |>.PositionInFundamentalSquare position
  exact
    standardNormalizedAssembledVertexPositions_inside
      presentation.toPlanarIncidencePresentation

/-- A finite route certificate completes the global continuously planar
geometry of the corrected ribbon assembly.  The two vertex obligations are
already discharged by normalization. -/
def normalizedRibbonContinuousAssemblyGeometryOfFinite
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (certificate :
      FiniteContinuousAssemblyPlanarityCertificate
        (normalizedRibbonThreeStrandRouting presentation)) :
    ContinuousAssemblyGeometry
      (normalizedRibbonThreeStrandRouting presentation) :=
  certificate.toContinuousAssemblyGeometry
    (normalizedRibbonAssembledVertexPositions_nodup presentation)
    (normalizedRibbonAssembledVertexPositions_inside presentation)

/-- Doubling changes the standard period and gadget origins coherently, so
the padded corrected assembly retains pairwise distinct gadget vertices. -/
theorem paddedNormalizedRibbonAssembledVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    (assembledVertexPositions
      (paddedNormalizedRibbonThreeStrandRouting presentation)).Nodup := by
  change
    (assembledVertexPositions
      (standardNormalizedThreeStrandRouting
        (presentation.scaleTwo).toHaloBoundedContinuousPlanarIncidencePresentation)).Nodup
  exact
    standardNormalizedAssembledVertexPositions_nodup
      presentation.scaleTwo.toPlanarIncidencePresentation

/-- Every padded corrected assembled gadget vertex lies in the doubled,
refined fundamental square. -/
theorem paddedNormalizedRibbonAssembledVertexPositions_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    ∀ position ∈
        assembledVertexPositions
          (paddedNormalizedRibbonThreeStrandRouting presentation),
      (assembledDrawing
        (paddedNormalizedRibbonThreeStrandRouting presentation))
        |>.PositionInFundamentalSquare position := by
  change
    ∀ position ∈
        assembledVertexPositions
          (standardNormalizedThreeStrandRouting
            (presentation.scaleTwo).toHaloBoundedContinuousPlanarIncidencePresentation),
      (assembledDrawing
        (standardNormalizedThreeStrandRouting
          (presentation.scaleTwo).toHaloBoundedContinuousPlanarIncidencePresentation))
        |>.PositionInFundamentalSquare position
  exact
    standardNormalizedAssembledVertexPositions_inside
      presentation.scaleTwo.toPlanarIncidencePresentation

/-- For the padded corrected routing, the endpoint and vertex bounds are
proved; these are exactly the three remaining executable continuous
planarity checks. -/
structure PaddedNormalizedRibbonFiniteContinuousPlanarityChecks
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    Prop where
  routesChecked :
    (assembledDrawing
      (paddedNormalizedRibbonThreeStrandRouting presentation)
      |>.expandedFiniteRoutesAvoidInteriors) = true
  verticesChecked :
    (assembledDrawing
      (paddedNormalizedRibbonThreeStrandRouting presentation)
      |>.finiteVerticesAvoidRouteInteriors) = true
  continuousChecked :
    (assembledDrawing
      (paddedNormalizedRibbonThreeStrandRouting presentation)
      |>.expandedFiniteRoutesHaveDisjointInteriors) = true

namespace PaddedNormalizedRibbonFiniteContinuousPlanarityChecks

/-- Add the proved padded endpoint theorem to obtain the generic finite
continuous assembly certificate. -/
def toFiniteContinuousAssemblyPlanarityCertificate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement}
    (checks :
      PaddedNormalizedRibbonFiniteContinuousPlanarityChecks presentation) :
    FiniteContinuousAssemblyPlanarityCertificate
      (paddedNormalizedRibbonThreeStrandRouting presentation) where
  endpointBounds :=
    paddedNormalizedRibbonAssembledSegmentEndpointsInExpandedSquare
      presentation
  routesChecked := checks.routesChecked
  verticesChecked := checks.verticesChecked
  continuousChecked := checks.continuousChecked

end PaddedNormalizedRibbonFiniteContinuousPlanarityChecks

/-- A finite continuous route certificate completes the global geometry of
the final padded corrected assembly. -/
def paddedNormalizedRibbonContinuousAssemblyGeometryOfFinite
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (certificate :
      FiniteContinuousAssemblyPlanarityCertificate
        (paddedNormalizedRibbonThreeStrandRouting presentation)) :
    ContinuousAssemblyGeometry
      (paddedNormalizedRibbonThreeStrandRouting presentation) :=
  certificate.toContinuousAssemblyGeometry
    (paddedNormalizedRibbonAssembledVertexPositions_nodup presentation)
    (paddedNormalizedRibbonAssembledVertexPositions_inside presentation)

/-- Equivalently, the three executable checks alone complete the global
continuous geometry of the padded corrected assembly. -/
noncomputable def paddedNormalizedRibbonContinuousAssemblyGeometryOfChecks
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (checks :
      PaddedNormalizedRibbonFiniteContinuousPlanarityChecks presentation) :
    ContinuousAssemblyGeometry
      (paddedNormalizedRibbonThreeStrandRouting presentation) :=
  paddedNormalizedRibbonContinuousAssemblyGeometryOfFinite
    presentation
    checks.toFiniteContinuousAssemblyPlanarityCertificate

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
