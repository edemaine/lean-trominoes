/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceTransverseSeparation
import LeanTrominoes.ScaledRectangleLinearNeighborhoodSeparation

/-!
# Piecewise separation from a retained outer fan

The retained source construction need not put an entire route prefix on
one side of another terminal line, nor keep every piece outside the
terminal segment's endpoint rectangle.  The correct finite obligation is
piecewise: each point and each relevant segment may use whichever of
those two separating axes works locally.

This file specializes the generic mixed-neighborhood theorem to the
radius-65 longitudinal and radius-845 transverse bounds of retained outer
radial routes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every point and axis-aligned segment of the source prefix clears the
discarded reference segment through at least one of its two natural
separating axes. -/
def SourcePrefixCorridorSeparated
    (sourceRoute referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) : Prop :=
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  let referenceCenter := referenceRoute.getLastD (0, 0)
  let normal :=
    retainedTerminalFanOuterTransverseNormal referenceDirection
  (∀ point ∈ sourceRoute.dropLast,
      PointSeparatesRectangleOrLine
        point
        referenceSegment.coordinateLower
        referenceSegment.coordinateUpper
        referenceCenter normal) ∧
    ∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
      segment.IsAxisAligned →
        SegmentSeparatesRectangleOrLine
          segment
          referenceSegment.coordinateLower
          referenceSegment.coordinateUpper
          referenceCenter normal

instance
    (sourceRoute referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) :
    Decidable
      (SourcePrefixCorridorSeparated
        sourceRoute referenceRoute referenceDirection) := by
  unfold SourcePrefixCorridorSeparated
  infer_instance

/-- Piecewise longitudinal-or-transverse separation clears the complete
outer radial route around an arbitrary retained terminal. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_corridorSeparated
    {factor : Nat} (factorPositive : 0 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceSeparated :
      SourcePrefixCorridorSeparated
        sourceRoute referenceRoute referenceTerminal.1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterRadialRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor referenceRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  let combinedFactor :=
    retainedTerminalFanTotalRefinement * factor
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  let referenceCenter := referenceRoute.getLastD (0, 0)
  let normal :=
    retainedTerminalFanOuterTransverseNormal referenceTerminal.1
  let radialRoute :=
    retainedTerminalFanOuterRadialRoute
      (Cell.scale combinedFactor referenceCenter)
      (scaleRetainedTerminalData factor referenceTerminal)
      referenceSlot
  have combinedPositive : 0 < combinedFactor := by
    dsimp [combinedFactor]
    exact Nat.mul_pos (by native_decide) factorPositive
  have rectangleClearance : 65 < combinedFactor := by
    dsimp [combinedFactor]
    rw [retainedTerminalFanTotalRefinement_eq]
    omega
  have transverseClearance : 845 < combinedFactor := by
    simpa [combinedFactor] using clearance
  change
    (∀ point ∈ sourceRoute.dropLast,
        PointSeparatesRectangleOrLine
          point
          referenceSegment.coordinateLower
          referenceSegment.coordinateUpper
          referenceCenter normal) ∧
      (∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
        segment.IsAxisAligned →
          SegmentSeparatesRectangleOrLine
            segment
            referenceSegment.coordinateLower
            referenceSegment.coordinateUpper
            referenceCenter normal)
    at sourceSeparated
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_rectangleOrLinearNeighborhood
      (source := sourceRoute.dropLast)
      (nearby := radialRoute)
      (referenceLower := referenceSegment.coordinateLower)
      (referenceUpper := referenceSegment.coordinateUpper)
      (referenceCenter := referenceCenter)
      (normal := normal)
      (factor := combinedFactor)
      (rectangleRadius := 65)
      (linearRadius := 845)
      combinedPositive rectangleClearance transverseClearance
      sourceSeparated.1 sourceSeparated.2
      (by
        intro point pointMember
        have centerEq :
            Cell.scale combinedFactor referenceCenter =
              Cell.scale retainedTerminalFanTotalRefinement
                ((scalePolyline factor referenceRoute).getLastD
                  (0, 0)) := by
          rw [scalePolyline_getLastD]
          simp [combinedFactor, referenceCenter,
            Cell.scale_scale, Nat.cast_mul]
        have pointMember' :
            point ∈
              retainedTerminalFanOuterRadialRoute
                (Cell.scale retainedTerminalFanTotalRefinement
                  ((scalePolyline factor referenceRoute).getLastD
                    (0, 0)))
                (scaleRetainedTerminalData factor referenceTerminal)
                referenceSlot := by
          rw [← centerEq]
          simpa [radialRoute] using pointMember
        simpa [combinedFactor, referenceSegment, referenceCenter] using
          retainedTerminalFanOuterRadialRoute_point_in_scaledFinalSegmentRectangle
            referenceRoute referenceTerminal referenceSlot
            referenceLength referenceClassified pointMember')
      (by
        intro point pointMember
        simpa [radialRoute, normal] using
          retainedTerminalFanOuterRadialRoute_transverse_band
            (Cell.scale combinedFactor referenceCenter)
            (scaleRetainedTerminalData factor referenceTerminal)
            referenceSlot pointMember)
  rw [scalePolyline_getLastD]
  simpa [radialRoute, combinedFactor, referenceCenter,
    scalePolyline_scalePolyline_nat,
    scalePolyline, List.map_map, Function.comp_def,
    Cell.scale_scale, Nat.cast_mul] using separated

/-- In the final retained drawing, the piecewise corridor certificate is
the only new geometric premise needed to clear another complete fan. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_corridorSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondCenter : Cell}
    (firstMember :
      (firstRoute, firstIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (secondRoute, secondIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstHead : firstRoute.head? = some firstSource)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (sourceNeCenter : firstSource ≠ secondCenter)
    (secondTerminal : RetainedTerminalData)
    (secondSlot : RetainedTerminalSlot)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (corridorSeparated :
      SourcePrefixCorridorSeparated
        firstRoute secondRoute secondTerminal.1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor secondCenter))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale factor secondCenter)
  let scaledTerminal :=
    scaleRetainedTerminalData factor secondTerminal
  have factorPositive : 0 < factor := by
    omega
  have secondLastD :
      secondRoute.getLastD (0, 0) = secondCenter := by
    simp [List.getLastD_eq_getLast?, secondLast]
  have radialAvoid :=
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_corridorSeparated
      factorPositive clearance firstRoute secondRoute
      secondTerminal secondSlot secondLength secondClassified
      corridorSeparated
  have localAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterLocalRoute
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne firstMember secondMember
      firstLength secondLength indicesDifferent firstHead secondLast
      sourceNeCenter secondTerminal.1 secondSlot
  have scaledLengthPositive : 0 < scaledTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos factorPositive
      (retainedTerminalDirectionClassify_sound secondClassified).1
  have radialAvoid' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterRadialRoute
          center scaledTerminal secondSlot) := by
    rw [scalePolyline_getLastD, secondLastD] at radialAvoid
    simpa [center, scaledTerminal] using radialAvoid
  have localAvoid' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterLocalRouteAt
          center scaledTerminal.1 secondSlot) := by
    simpa [center, scaledTerminal] using localAvoid
  rw [retainedTerminalFanOuterCompleteRoute]
  exact
    radialAvoid'.join_right localAvoid'
      (retainedTerminalFanOuterRadialRoute_getLast?
        center scaledTerminal secondSlot scaledLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center scaledTerminal.1 secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
