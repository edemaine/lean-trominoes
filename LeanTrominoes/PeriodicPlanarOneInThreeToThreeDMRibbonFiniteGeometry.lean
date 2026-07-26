import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMFiniteGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds

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

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
