import LeanTrominoes.RetainedAngularFanSourceLocalSeparation
import LeanTrominoes.RetainedAngularFanOuterSourceAlignment
import LeanTrominoes.ScaledSegmentNeighborhoodSeparation

/-!
# Separating a refined source prefix from an outer radial fan

The radial part of an outer fan stays in a radius-65 tube around the
discarded final segment of its source route.  When that final segment is
axis-aligned, the general scaled-segment neighborhood theorem turns the
old contact-free prefix/segment certificate into strict separation from
the whole radial route.

The routed-clause terminal directions are diagonal and require a separate
exact argument; this file deliberately records the axis-aligned case
without hiding that remaining obligation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A nonnegative scale factor commutes with the lower endpoint corner of
a segment. -/
@[simp]
theorem GridSegment.coordinateLower_scale
    {factor : Int} (factorNonnegative : 0 ≤ factor)
    (segment : GridSegment) :
    (segment.scale factor).coordinateLower =
      Cell.scale factor segment.coordinateLower := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [GridSegment.scale, GridSegment.coordinateLower,
    Cell.scale,
    mul_min_of_nonneg startX finishX factorNonnegative,
    mul_min_of_nonneg startY finishY factorNonnegative]

/-- A nonnegative scale factor commutes with the upper endpoint corner of
a segment. -/
@[simp]
theorem GridSegment.coordinateUpper_scale
    {factor : Int} (factorNonnegative : 0 ≤ factor)
    (segment : GridSegment) :
    (segment.scale factor).coordinateUpper =
      Cell.scale factor segment.coordinateUpper := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [GridSegment.scale, GridSegment.coordinateUpper,
    Cell.scale,
    mul_max_of_nonneg startX finishX factorNonnegative,
    mul_max_of_nonneg startY finishY factorNonnegative]

/-- After source-first refinement, the source-centered outer corridor axis
is exactly the combined scaling of the discarded final source segment. -/
theorem retainedTerminalFanSourceCorridorAxis_eq_scale_finalSegment
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal) :
    retainedTerminalFanSourceCorridorAxis
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor route).getLastD (0, 0)))
        (scaleRetainedTerminalData factor terminal) =
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment).scale
        (retainedTerminalFanTotalRefinement * factor) := by
  rw [polylineLastEntrance_eq_retainedTerminalSplicePoint
    routeLength classified]
  simp only [scalePolyline_getLastD]
  rcases route.getLastD (0, 0) with ⟨targetX, targetY⟩
  rcases terminal with ⟨direction, length⟩
  rcases direction.primitive with ⟨primitiveX, primitiveY⟩
  simp [retainedTerminalFanSourceCorridorAxis,
    retainedTerminalSplicePoint,
    scaleRetainedTerminalData,
    GridSegment.scale, Cell.add, Cell.scale] <;>
    ring_nf <;>
    simp

/-- Every radial-route point lies in the radius-65 expansion of the
combined-scaled endpoint rectangle of its discarded source segment. -/
theorem retainedTerminalFanOuterRadialRoute_point_in_scaledFinalSegmentRectangle
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterRadialRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal)
          slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 65
      (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateLower))
      (coordinateRadiusUpper 65
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper))
      point := by
  have productNonnegativeInt :
      (0 : Int) ≤
        retainedTerminalFanTotalRefinement * factor := by
    exact_mod_cast
      Nat.zero_le
        (retainedTerminalFanTotalRefinement * factor)
  have checkpointBound :=
    retainedTerminalFanOuterRadialRoute_point_in_tube
      (Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor route).getLastD (0, 0)))
      (scaleRetainedTerminalData factor terminal)
      slot pointMember
  have sourceBound :=
    inCoordinateCheckpointTube_outerInward_to_sourceTerminal
      65
      (Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor route).getLastD (0, 0)))
      (scaleRetainedTerminalData factor terminal)
      slot checkpointBound
  have rectangleBound :=
    inCoordinateSourceTerminalTube_in_coordinateRectangle
      sourceBound
  rw [
    retainedTerminalFanSourceCorridorAxis_eq_scale_finalSegment
      route terminal routeLength classified,
    GridSegment.coordinateLower_scale
      productNonnegativeInt,
    GridSegment.coordinateUpper_scale
      productNonnegativeInt] at rectangleBound
  exact rectangleBound

/-- A source prefix is longitudinally separated from a discarded terminal
segment when each listed point, and each axis-aligned segment that can
participate in the orthogonal contact predicate, has a disjoint endpoint
rectangle. -/
def SourcePrefixRectangularlySeparated
    (sourceRoute referenceRoute : List Cell) : Prop :=
  let reference : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  (∀ point ∈ sourceRoute.dropLast,
      ClosedGridRectanglesSeparated
        point point
        reference.coordinateLower reference.coordinateUpper) ∧
    ∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
      segment.IsAxisAligned →
        ClosedGridRectanglesSeparated
          segment.coordinateLower segment.coordinateUpper
          reference.coordinateLower reference.coordinateUpper

instance (sourceRoute referenceRoute : List Cell) :
    Decidable
      (SourcePrefixRectangularlySeparated
        sourceRoute referenceRoute) := by
  unfold SourcePrefixRectangularlySeparated
  infer_instance

/-- Longitudinal rectangle separation clears an outer radial route around
an arbitrary retained terminal direction, including a diagonal one. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_rectangleSeparated
    {factor : Nat} (factorPositive : 0 < factor)
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceSeparated :
      SourcePrefixRectangularlySeparated
        sourceRoute referenceRoute) :
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
  have combinedPositive : 0 < combinedFactor := by
    dsimp [combinedFactor]
    exact Nat.mul_pos (by native_decide) factorPositive
  have radiusLt : 65 < combinedFactor := by
    dsimp [combinedFactor]
    rw [retainedTerminalFanTotalRefinement_eq]
    omega
  change
    (∀ point ∈ sourceRoute.dropLast,
        ClosedGridRectanglesSeparated
          point point
          referenceSegment.coordinateLower
          referenceSegment.coordinateUpper) ∧
      (∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
        segment.IsAxisAligned →
          ClosedGridRectanglesSeparated
            segment.coordinateLower segment.coordinateUpper
            referenceSegment.coordinateLower
            referenceSegment.coordinateUpper)
    at sourceSeparated
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_rectangleNeighborhood
      (source := sourceRoute.dropLast)
      (nearby :=
        retainedTerminalFanOuterRadialRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor referenceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor referenceTerminal)
          referenceSlot)
      (referenceLower := referenceSegment.coordinateLower)
      (referenceUpper := referenceSegment.coordinateUpper)
      combinedPositive radiusLt
      sourceSeparated.1 sourceSeparated.2
      (by
        intro point pointMember
        simpa [combinedFactor, referenceSegment] using
          retainedTerminalFanOuterRadialRoute_point_in_scaledFinalSegmentRectangle
            referenceRoute referenceTerminal referenceSlot
            referenceLength referenceClassified pointMember)
  simpa [combinedFactor, scalePolyline_scalePolyline_nat,
    scalePolyline, List.map_map, Function.comp_def,
    Cell.scale_scale, Nat.cast_mul] using separated

/-- A source-first refined prefix strictly avoids the radial part of a
second fan whenever the discarded final source segment is axis-aligned
and was strictly separated before refinement. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_axisAligned
    {factor : Nat} (factorPositive : 0 < factor)
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (referenceAligned :
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (sourceAvoids :
      RoutesStrictlyAvoidEachOther
        sourceRoute.dropLast
        [polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)]) :
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
  have combinedPositive : 0 < combinedFactor := by
    dsimp [combinedFactor]
    exact Nat.mul_pos (by native_decide) factorPositive
  have radiusLt : 65 < combinedFactor := by
    dsimp [combinedFactor]
    rw [retainedTerminalFanTotalRefinement_eq]
    omega
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_axisAlignedSegmentNeighborhood
      (source := sourceRoute.dropLast)
      (nearby :=
        retainedTerminalFanOuterRadialRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor referenceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor referenceTerminal)
          referenceSlot)
      (reference := referenceSegment)
      combinedPositive radiusLt
      (by simpa [referenceSegment] using referenceAligned)
      (by simpa [referenceSegment] using sourceAvoids)
      (by
        intro point pointMember
        simpa [combinedFactor, referenceSegment] using
          retainedTerminalFanOuterRadialRoute_point_in_scaledFinalSegmentRectangle
            referenceRoute referenceTerminal referenceSlot
            referenceLength referenceClassified pointMember)
  simpa [combinedFactor, scalePolyline_scalePolyline_nat,
    scalePolyline, List.map_map, Function.comp_def,
    Cell.scale_scale, Nat.cast_mul] using separated

/-- The retained drawing's final-segment certificate supplies the
axis-aligned radial separation hypotheses for two distinct source routes. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterRadialRoute_of_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {factor : Nat} (factorPositive : 0 < factor)
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
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (sourceNeCenter : firstSource ≠ secondCenter)
    (secondTerminal : RetainedTerminalData)
    (secondSlot : RetainedTerminalSlot)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (secondFinalSegmentAligned :
      (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
        GridSegment).IsAxisAligned) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast
      (retainedTerminalFanOuterRadialRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor secondCenter))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have secondLastD :
      secondRoute.getLastD (0, 0) = secondCenter := by
    simp [List.getLastD_eq_getLast?, secondLast]
  have sourceAvoids :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherFinalSegment
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      sourceNeCenter
  rw [← secondLastD] at secondFinalSegmentAligned
  rw [← secondLastD] at sourceAvoids
  have separated :=
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_axisAligned
      factorPositive firstRoute secondRoute secondTerminal secondSlot
      secondLength secondClassified
      secondFinalSegmentAligned sourceAvoids
  rw [scalePolyline_getLastD, secondLastD] at separated
  exact separated

/-- For an axis-aligned discarded terminal segment, the refined source
prefix avoids the complete radial-plus-local fan of another route. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_axisAligned
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
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (sourceNeCenter : firstSource ≠ secondCenter)
    (secondTerminal : RetainedTerminalData)
    (secondSlot : RetainedTerminalSlot)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (secondFinalSegmentAligned :
      (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
        GridSegment).IsAxisAligned) :
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
  have radialAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterRadialRoute_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorPositive firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      sourceNeCenter secondTerminal secondSlot secondClassified
      secondFinalSegmentAligned
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
