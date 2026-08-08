import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanCompatibilityTransport
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedRouteLength
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-!
# Padded normalized coordinated ribbon routing

This is the final occurrence-routing object: double the ribbon-ready source,
normalize its clause anchors, install the coordinated endpoint fans, and join
them to the three colored corridor cores.  The padding length theorem and the
transported clockwise-order certificate make separation unconditional from
the source promises.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Width three survives source doubling and anchor normalization. -/
theorem paddedNormalizedSource_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (width : source.erase.WidthAtMost 3) :
    (normalizedPositionedSource
      (source.scale 2) (placement.scale 2)).erase.WidthAtMost 3 := by
  simpa [normalizedPositionedSource] using
    PeriodicCNF.anchorNormalize_widthAtMost
      (source.scale 2).erase 3 (by simpa using width)

/-- The final coordinated routing on the doubled, normalized source. -/
noncomputable def paddedNormalizedCoordinatedRibbonThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    ThreeStrandRouting
      (normalizedPositionedSource
        (source.scale 2) (placement.scale 2)).erase :=
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  coordinatedSourceRibbonThreeStrandRouting
    normalized
    (paddedNormalizedSource_widthAtMostThree width)
    (paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered)

set_option maxHeartbeats 1000000 in
/-- Every pair of distinct colored occurrence routes in the final
coordinated routing is contact-free. -/
theorem paddedNormalizedCoordinatedRibbonThreeStrandRoutes_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes)
    {first second :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      ((paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered).route first firstColor)
      ((paddedNormalizedCoordinatedRibbonThreeStrandRouting
        presentation width occurrences arity
        variableOrdered clauseOrdered).route second secondColor) := by
  let normalized :=
    normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
  let compatible :=
    paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
      presentation width occurrences arity variableOrdered clauseOrdered
  apply coordinatedSourceRibbonThreeStrandRoutes_strictlyAvoidEachOther
    normalized
    (paddedNormalizedSource_widthAtMostThree width)
    compatible
    (paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three presentation)
    different

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
