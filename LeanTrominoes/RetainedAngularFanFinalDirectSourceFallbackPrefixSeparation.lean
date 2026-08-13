/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private theorem scalePolyline_dropLast_int
    (factor : Int)
    (route : List Cell) :
    (scalePolyline factor route).dropLast =
      scalePolyline factor route.dropLast := by
  induction route with
  | nil =>
      rfl
  | cons point route induction =>
      cases route with
      | nil =>
          rfl
      | cons next rest =>
          simp [scalePolyline]

private theorem scalePolyline_scalePolyline_int
    (first second : Int)
    (route : List Cell) :
    scalePolyline first (scalePolyline second route) =
      scalePolyline (first * second) route := by
  induction route with
  | nil =>
      rfl
  | cons point route induction =>
      simp [scalePolyline, Cell.scale_scale]

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

/-- Translating the local Figure 7 adapter by a direct choice's physical
offset is the same as constructing it at the positioned fan center. -/
theorem RetainedDirectSourceRouteChoice.positionedLocalRoute_eq
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedTerminalFanOuterLocalRouteAt
          (retainedDirectSourceFanCenterAt
            choice.kind choice.index)
          (retainedDirectSourceFanTerminalAt
            choice.kind choice.index).1
          slot) =
      retainedTerminalFanOuterLocalRouteAt
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        slot := by
  unfold PeriodicOrthocrossing.translatePolyline
    retainedTerminalFanOuterLocalRouteAt
    retainedDirectSourcePositionedFanCenterAt
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases point with ⟨pointX, pointY⟩
  rcases retainedDirectSourceFanPositioningOffset choice.origin with
    ⟨offsetX, offsetY⟩
  rcases retainedDirectSourceFanCenterAt choice.kind choice.index with
    ⟨centerX, centerY⟩
  simp [Cell.add]
  constructor <;> ring

/-- Positioning a direct choice transports the shifted radial tail's finite
radius-65 bound to the represented physical source segment. -/
theorem
    RetainedDirectSourceRouteChoice.shiftedTail_point_in_sourceSegmentRectangle
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index)
            slot)) :
    InClosedGridRectangle
      (coordinateRadiusLower 65
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 65
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      point := by
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  let localSegment : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt
        choice.kind choice.index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt
        choice.kind choice.index).getLastD (0, 0)⟩
  let positioningOffset :=
    retainedDirectSourceFanPositioningOffset choice.origin
  have localBound :=
    retainedDirectSourceFanShiftedTailAt_point_in_scaledLocalSegmentRectangle
      choice.kind choice.index slot localPoint localPointMember
  have lowerEq :
      Cell.add positioningOffset
          (coordinateRadiusLower 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower)) =
        coordinateRadiusLower 65
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateLower, coordinateRadiusLower,
      Cell.add, Cell.scale, min_add_add_left]
    constructor <;> ring
  have upperEq :
      Cell.add positioningOffset
          (coordinateRadiusUpper 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper)) =
        coordinateRadiusUpper 65
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper) := by
    rcases choice.origin with ⟨originX, originY⟩
    rcases localSegment.start with ⟨startX, startY⟩
    rcases localSegment.finish with ⟨finishX, finishY⟩
    simp [localSegment, positioningOffset,
      RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceFanPositioningOffset,
      GridSegment.coordinateUpper, coordinateRadiusUpper,
      Cell.add, Cell.scale, max_add_add_left]
    constructor <;> ring
  rw [← lowerEq, ← upperEq]
  simpa [localSegment, positioningOffset] using
    PeriodicOrthocrossing.InClosedGridRectangle.add
      localBound positioningOffset

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

/-- Unlike the full routed-clause direct route, every shifted radial tail
fits the ordinary rectangle-and-transverse corridor.  Thus the same source
corridor certificate separates it for all direct atlas kinds. -/
theorem
    retainedSourceScaledPrefix_strictlyAvoids_directShiftedTail_of_corridorSeparated
    (sourceRoute referenceRoute : List Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
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
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedTerminalFanOuterEscapedShiftedTail
          (retainedDirectSourceFanCenterAt
            choice.kind choice.index)
          (retainedDirectSourceFanTerminalAt
            choice.kind choice.index)
          slot)) := by
  have referenceCenterEq :
      referenceRoute.getLastD (0, 0) =
        choice.sourceSegment.finish :=
    congrArg GridSegment.finish referenceSegmentEq
  unfold SourcePrefixCorridorSeparated at sourceSeparated
  rw [referenceSegmentEq, referenceCenterEq] at sourceSeparated
  apply
    routesStrictlyAvoidEachOther_scalePolyline_rectangleOrLinearNeighborhood
      (factor := retainedTerminalFanTotalRefinement * 4)
      (rectangleRadius := 65)
      (linearRadius := 845)
      (source := sourceRoute.dropLast)
      (nearby :=
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index)
            slot))
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
    exact choice.shiftedTail_point_in_sourceSegmentRectangle
      slot pointMember
  · intro point pointMember
    have bounded := choice.shiftedTail_transverse_band
      slot pointMember
    rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish]
      at bounded
    exact bounded

/-- The retained drawing's distinct-endpoint certificate transports the
standard local-adapter separation theorem to a checked direct choice. -/
theorem retainedFinalSourceScaledPrefix_strictlyAvoids_directLocalRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (sourceRoute : List Cell)
    (sourceIndex directIndex : Nat)
    (sourcePoint directCenter : Cell)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (directMember :
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex,
        directIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (directLength :
      2 ≤
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).length)
    (indicesDifferent : sourceIndex ≠ directIndex)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (directLast :
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).getLast? =
        some directCenter)
    (sourceNeCenter : sourcePoint ≠ directCenter)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedTerminalFanOuterLocalRouteAt
          (retainedDirectSourceFanCenterAt
            choice.kind choice.index)
          (retainedDirectSourceFanTerminalAt
            choice.kind choice.index).1
          slot)) := by
  have directLastD :
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).getLastD (0, 0) =
        directCenter := by
    simp [List.getLastD_eq_getLast?, directLast]
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula clauseIndex literalIndex choice choiceLookup
  have choiceFinishEq : choice.sourceSegment.finish = directCenter := by
    have representedFinish :=
      congrArg GridSegment.finish representedSegment
    rw [directLastD] at representedFinish
    exact representedFinish.symm
  have localAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterLocalRoute
      formula wellFormed degree isLocal clausesNonempty
      (factor := 4)
      (firstRoute := sourceRoute)
      (secondRoute :=
        PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)
      (firstIndex := sourceIndex)
      (secondIndex := directIndex)
      (firstSource := sourcePoint)
      (secondCenter := directCenter)
      (by omega)
      sourceMember directMember sourceLength directLength
      indicesDifferent sourceHead directLast sourceNeCenter
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      slot
  have centerEq :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale 4 directCenter) := by
    rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish,
      choiceFinishEq]
    simp [Cell.scale_scale]
  rw [scalePolyline_dropLast_int,
    scalePolyline_dropLast_int,
    scalePolyline_scalePolyline_int] at localAvoid
  rw [choice.positionedLocalRoute_eq, centerEq]
  exact localAvoid

/-- If a source prefix avoids both post-escape pieces, it avoids their
positioned endpoint join: the direct route's entire fixed complete tail. -/
theorem retainedSourcePrefix_strictlyAvoids_directCompleteTail
    (sourcePrefix : List Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (shiftedAvoid :
      RoutesStrictlyAvoidEachOther
        sourcePrefix
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index)
            slot)))
    (localAvoid :
      RoutesStrictlyAvoidEachOther
        sourcePrefix
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1
            slot))) :
    RoutesStrictlyAvoidEachOther
      sourcePrefix
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanCompleteTailAt
          choice.kind choice.index slot)) := by
  let offset :=
    retainedDirectSourceFanPositioningOffset choice.origin
  let center :=
    retainedDirectSourceFanCenterAt choice.kind choice.index
  let terminal :=
    retainedDirectSourceFanTerminalAt choice.kind choice.index
  let boundary :=
    Cell.add offset
      (retainedTerminalFanOuterLanePort
        center terminal.1 slot)
  have shiftedLast :
      (PeriodicOrthocrossing.translatePolyline offset
        (retainedTerminalFanOuterEscapedShiftedTail
          center terminal slot)).getLast? =
        some boundary := by
    have localLast :=
      retainedTerminalFanOuterEscapedShiftedTail_getLast?
        center terminal slot
        (retainedDirectSourceFanTerminalAt_length_positive
          choice.kind choice.index)
        (retainedDirectSourceFanTerminalAt_escape_fits
          choice.kind choice.index)
    simpa [PeriodicOrthocrossing.translatePolyline,
      List.getLast?_map, offset, center, terminal, boundary] using
      congrArg (Option.map (Cell.add offset)) localLast
  have localHead :
      (PeriodicOrthocrossing.translatePolyline offset
        (retainedTerminalFanOuterLocalRouteAt
          center terminal.1 slot)).head? =
        some boundary := by
    have localHead :=
      retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot
    simp [PeriodicOrthocrossing.translatePolyline,
      offset, center, terminal, boundary, localHead]
  unfold retainedDirectSourceFanCompleteTailAt
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail
  rw [translatePolyline_joinAtEndpoint]
  exact shiftedAvoid.join_right localAvoid shiftedLast localHead

/-- For a distinct retained source incidence, the corridor certificate and
the endpoint-clearance certificate together clear every post-escape piece
of a selected direct route, including routed-clause choices. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteTail_of_corridorSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (sourceRoute : List Cell)
    (sourceIndex directIndex : Nat)
    (sourcePoint directCenter : Cell)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (directMember :
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex,
        directIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (directLength :
      2 ≤
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).length)
    (indicesDifferent : sourceIndex ≠ directIndex)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (directLast :
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).getLast? =
        some directCenter)
    (sourceNeCenter : sourcePoint ≠ directCenter)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
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
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanCompleteTailAt
          choice.kind choice.index slot)) := by
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula clauseIndex literalIndex choice choiceLookup
  have shiftedAvoid :=
    retainedSourceScaledPrefix_strictlyAvoids_directShiftedTail_of_corridorSeparated
      sourceRoute
      (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex)
      choice slot representedSegment sourceSeparated
  have localAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_directLocalRoute
      formula wellFormed degree isLocal clausesNonempty
      sourceRoute sourceIndex directIndex sourcePoint directCenter
      clauseIndex literalIndex choice slot
      sourceMember directMember sourceLength directLength
      indicesDifferent sourceHead directLast sourceNeCenter choiceLookup
  exact
    retainedSourcePrefix_strictlyAvoids_directCompleteTail
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      choice slot shiftedAvoid localAvoid

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
