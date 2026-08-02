import LeanTrominoes.RetainedAngularFanDirectSourceTransverseBounds
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherCycleSeparation
import LeanTrominoes.RetainedAngularFanSourceMixedSeparation

/-!
# Fallback prefixes avoid non-routed direct source routes

A selected direct route is a bounded replacement for the ordinary outer
fan around its represented two-point source segment.  For crossover and
routed-variable choices, the radius-288 coordinate rectangle and radius-495
transverse band both fit inside the final factor-1152 source clearance.
Consequently the existing rectangle-or-line corridor certificate separates
any other retained source prefix from the selected direct route.

The routed-clause atlas kind has a wider coordinated escape and is left to
the specialized routed-clause/carrier interface argument.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The positioned fan center of a checked direct choice is the fully
refined image of its represented source-segment endpoint. -/
theorem
    RetainedDirectSourceRouteChoice.positionedFanCenter_eq_scale_sourceSegment_finish
    (choice : RetainedDirectSourceRouteChoice) :
    retainedDirectSourcePositionedFanCenterAt
        choice.origin choice.kind choice.index =
      Cell.scale
        (retainedTerminalFanTotalRefinement * 4)
        choice.sourceSegment.finish := by
  rcases choice with ⟨⟨originX, originY⟩, kind, index⟩
  have scaledLast :
      (scalePolyline (4 : Int)
          (retainedDirectSourceLocalRouteAt kind index)).getLastD
            (0, 0) =
        Cell.scale 4
          ((retainedDirectSourceLocalRouteAt kind index).getLastD
            (0, 0)) := by
    simpa using
      scalePolyline_getLastD 4
        (retainedDirectSourceLocalRouteAt kind index)
  unfold retainedDirectSourcePositionedFanCenterAt
    retainedDirectSourceFanPositioningOffset
    retainedDirectSourceFanCenterAt
    RetainedDirectSourceRouteChoice.sourceSegment
  simp only
  rw [scaledLast]
  rcases (retainedDirectSourceLocalRouteAt
    kind index).getLastD (0, 0) with
    ⟨finishX, finishY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

/-- A successful final choice's represented source segment is exactly the
discarded final segment of the corresponding two-point retained route. -/
theorem retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    (⟨polylineLastEntrance
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex),
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).getLastD (0, 0)⟩ :
        GridSegment) =
      choice.sourceSegment := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  have localLength :=
    retainedDirectSourceLocalRouteAt_length choice.kind choice.index
  rcases List.length_eq_two.mp localLength with
    ⟨localHead, localLast, localRouteEq⟩
  rw [PeriodicOrthocrossing.finalCoordinatedSourceRoutes,
    ← represents]
  simp [localRouteEq, PeriodicOrthocrossing.translatePolyline,
    polylineLastEntrance, polylineFirstExit,
    RetainedDirectSourceRouteChoice.sourceSegment]

/-- A corridor certificate against the represented source segment strictly
separates its scaled source prefix from any non-routed selected direct
route. -/
theorem
    retainedSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
    (sourceRoute referenceRoute : List Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (kindNe : choice.kind ≠ .routedClause)
    (referenceSegmentEq :
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment) =
        choice.sourceSegment)
    (sourceSeparated :
      SourcePrefixCorridorSeparated
        sourceRoute referenceRoute
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (choice.completeRoute slot) := by
  have referenceCenterEq :
      referenceRoute.getLastD (0, 0) =
        choice.sourceSegment.finish :=
    congrArg GridSegment.finish referenceSegmentEq
  unfold SourcePrefixCorridorSeparated at sourceSeparated
  rw [referenceSegmentEq, referenceCenterEq] at sourceSeparated
  apply
    routesStrictlyAvoidEachOther_scalePolyline_rectangleOrLinearNeighborhood
      (factor := retainedTerminalFanTotalRefinement * 4)
      (rectangleRadius := 288)
      (linearRadius := 495)
      (source := sourceRoute.dropLast)
      (nearby := choice.completeRoute slot)
      (referenceLower := choice.sourceSegment.coordinateLower)
      (referenceUpper := choice.sourceSegment.coordinateUpper)
      (referenceCenter := choice.sourceSegment.finish)
      (normal :=
        retainedTerminalFanOuterTransverseNormal
          (retainedDirectSourceFanTerminalAt
            choice.kind choice.index).1)
  · native_decide
  · native_decide
  · native_decide
  · exact sourceSeparated.1
  · exact sourceSeparated.2
  · intro point pointMember
    exact choice.completeRoute_point_in_sourceSegmentRectangle
      slot pointMember
  · intro point pointMember
    have bounded :=
      choice.completeRoute_transverse_band_of_kind_ne_routedClause
        slot kindNe pointMember
    rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish]
      at bounded
    exact bounded

/-- Final-route specialization of the corridor bridge: the successful
choice lookup supplies the represented discarded segment automatically. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceRoute : List Cell)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (kindNe : choice.kind ≠ .routedClause)
    (sourceSeparated :
      SourcePrefixCorridorSeparated
        sourceRoute
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (choice.completeRoute slot) :=
  retainedSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
    sourceRoute
    (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex)
    choice slot kindNe
    (retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula clauseIndex literalIndex choice choiceLookup)
    sourceSeparated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
