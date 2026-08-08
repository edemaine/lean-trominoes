import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedFanSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-!
# Separation of complete periodically translated occurrence routes

The variable fan, central corridor, and clause fan have now been separated
pairwise in every relative orientation.  This file composes those nine
component pairs across the two certified endpoint joins.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A central corridor strictly avoids a forward nonzero translate of a
variable fan.  The proof reverses the relative frame and then translates both
routes back to the requested coordinates. -/
theorem occurrenceRibbonCorridorCore_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
      presentation compatible second first reverseTranslate
      (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
        presentation.toPlanarIncidencePresentation second first reverseNonzero)
      secondLength firstLength secondColor firstColor
  have shifted := backwards.translatePolyline forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero] at shifted
  simpa [backwardsPhysical, forwardsPhysical] using shifted.symm

/-- A clause fan strictly avoids a forward nonzero translate of a variable
fan, obtained from the variable/clause theorem in the reverse relative frame. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
      presentation compatible second first reverseTranslate reverseNonzero
      secondLength secondColor firstColor
  have shifted := backwards.translatePolyline forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero] at shifted
  simpa [backwardsPhysical, forwardsPhysical] using shifted.symm

set_option maxHeartbeats 800000 in
/-- Complete coordinated occurrence routes remain strictly separated from
every nonzero relative period translate, independently of their entries and
colors. -/
theorem coordinatedSourceRibbonThreeStrandRoute_strictlyAvoids_nonzeroTranslate_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      ((coordinatedSourceRibbonThreeStrandRouting
        presentation width compatible).route first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        ((coordinatedSourceRibbonThreeStrandRouting
          presentation width compatible).route second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  have routeKeysDifferent :=
    occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
      planar first second translateNonzero
  have firstVariableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible first firstColor
  have firstCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar first firstColor
  have firstClauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible first firstColor
  have secondVariableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible second secondColor
  have secondCoreEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar second secondColor
  have secondClauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible second secondColor
  have firstPrefixLast :
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub planar first firstColor)
        (occurrenceRibbonCorridorCore planar first firstColor)).getLast? =
          some (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase first firstColor)
            (occurrenceUnitSourceRoute planar first)) :=
    joinAtEndpoint_getLast?
      firstVariableEndpoints.2 firstCoreEndpoints.1 firstCoreEndpoints.2
  have secondTranslatedVariableLast :
      (translatePolyline physical
        (occurrenceCoordinatedRibbonVariableStub
          planar second secondColor)).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase second secondColor)
            (occurrenceUnitSourceRoute planar second))) :=
    translatePolyline_getLast?_eq_some physical _ _ secondVariableEndpoints.2
  have secondTranslatedCoreHead :
      (translatePolyline physical
        (occurrenceRibbonCorridorCore planar second secondColor)).head? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase second secondColor)
            (occurrenceUnitSourceRoute planar second))) :=
    translatePolyline_head?_eq_some physical _ _ secondCoreEndpoints.1
  have secondTranslatedCoreLast :
      (translatePolyline physical
        (occurrenceRibbonCorridorCore planar second secondColor)).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase second secondColor)
            (occurrenceUnitSourceRoute planar second))) :=
    translatePolyline_getLast?_eq_some physical _ _ secondCoreEndpoints.2
  have secondTranslatedClauseHead :
      (translatePolyline physical
        (occurrenceCoordinatedRibbonClauseStub
          planar second secondColor)).head? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase second secondColor)
            (occurrenceUnitSourceRoute planar second))) :=
    translatePolyline_head?_eq_some physical _ _ secondClauseEndpoints.1
  have secondPrefixLast :
      (joinAtEndpoint
        (translatePolyline physical
          (occurrenceCoordinatedRibbonVariableStub
            planar second secondColor))
        (translatePolyline physical
          (occurrenceRibbonCorridorCore
            planar second secondColor))).getLast? =
          some (Cell.add physical
            (ribbonCorridorRouteEnd
              (routedRibbonLane source.erase second secondColor)
              (occurrenceUnitSourceRoute planar second))) :=
    joinAtEndpoint_getLast?
      secondTranslatedVariableLast secondTranslatedCoreHead
        secondTranslatedCoreLast
  have variableVariable :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
      presentation compatible first second translate translateNonzero
      firstColor secondColor
  have variableCore :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
      presentation compatible first second translate routeKeysDifferent
      firstLength secondLength firstColor secondColor
  have variableClause :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
      presentation compatible first second translate translateNonzero
      firstLength firstColor secondColor
  have coreVariable :=
    occurrenceRibbonCorridorCore_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
      presentation compatible first second translate translateNonzero
      firstLength secondLength firstColor secondColor
  have coreCore :=
    occurrenceRibbonCorridorCore_strictlyAvoids_nonzeroTranslate_of_length_ge_three
      presentation first second translateNonzero firstLength secondLength
      firstColor secondColor
  have coreClause :=
    occurrenceRibbonCorridorCore_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
      presentation width compatible first second translate translateNonzero
      firstLength secondLength firstColor secondColor
  have clauseVariable :=
    occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
      presentation compatible first second translate translateNonzero
      secondLength firstColor secondColor
  have clauseCore :=
    occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
      presentation width compatible first second translate routeKeysDifferent
      firstLength secondLength firstColor secondColor
  have clauseClause :=
    occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
      presentation width compatible first second translate translateNonzero
      firstColor secondColor
  have firstFullAvoidsSecondVariable := by
    have prefixAvoid :=
      variableVariable.join_left coreVariable
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact prefixAvoid.join_left clauseVariable
      firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondCore := by
    have prefixAvoid :=
      variableCore.join_left coreCore
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact prefixAvoid.join_left clauseCore
      firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondClause := by
    have prefixAvoid :=
      variableClause.join_left coreClause
        firstVariableEndpoints.2 firstCoreEndpoints.1
    exact prefixAvoid.join_left clauseClause
      firstPrefixLast firstClauseEndpoints.1
  have firstFullAvoidsSecondPrefix :=
    firstFullAvoidsSecondVariable.join_right
      firstFullAvoidsSecondCore
      secondTranslatedVariableLast secondTranslatedCoreHead
  have fullAvoid :=
    firstFullAvoidsSecondPrefix.join_right
      firstFullAvoidsSecondClause
      secondPrefixLast secondTranslatedClauseHead
  change RoutesStrictlyAvoidEachOther
    (joinAtEndpoint
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub planar first firstColor)
        (occurrenceRibbonCorridorCore planar first firstColor))
      (occurrenceCoordinatedRibbonClauseStub planar first firstColor))
    (translatePolyline physical
      (joinAtEndpoint
        (joinAtEndpoint
          (occurrenceCoordinatedRibbonVariableStub planar second secondColor)
          (occurrenceRibbonCorridorCore planar second secondColor))
        (occurrenceCoordinatedRibbonClauseStub planar second secondColor)))
  rw [translatePolyline_joinAtEndpoint, translatePolyline_joinAtEndpoint]
  exact fullAvoid

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
