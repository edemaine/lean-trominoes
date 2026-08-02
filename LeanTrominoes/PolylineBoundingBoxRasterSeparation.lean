import LeanTrominoes.RetainedAngularFanSourceRasterSeparation

/-!
# Raster separation from enclosing route boxes

The mixed source-prefix/fan case does not require both source routes to be
orthogonal.  When the two relevant route pieces live in strictly separated
closed rectangles, their individual point and segment rectangles are
separated directly, regardless of the slopes of the second route.

This module turns that enclosing-box certificate into the exact
`SourcePolylineRectanglesSeparated` and retained-terminal corridor
certificates consumed by the factor-288 rasterization bridge.  It is the
generic adapter for route occurrences belonging to distinct planar-SAT
macrocells.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- If both endpoints of two segments lie in separated closed rectangles,
then the segments' own endpoint-coordinate rectangles are separated.  No
axis-alignment hypothesis is needed. -/
theorem GridSegment.coordinateRectanglesSeparated_of_inClosedGridRectangles
    {firstLower firstUpper secondLower secondUpper : Cell}
    {first second : GridSegment}
    (firstStart :
      InClosedGridRectangle firstLower firstUpper first.start)
    (firstFinish :
      InClosedGridRectangle firstLower firstUpper first.finish)
    (secondStart :
      InClosedGridRectangle secondLower secondUpper second.start)
    (secondFinish :
      InClosedGridRectangle secondLower secondUpper second.finish)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    ClosedGridRectanglesSeparated
      first.coordinateLower first.coordinateUpper
      second.coordinateLower second.coordinateUpper := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  simp only [InClosedGridRectangle]
    at firstStart firstFinish secondStart secondFinish
  simp only [ClosedGridRectanglesSeparated] at separated ⊢
  simp only [GridSegment.coordinateLower,
    GridSegment.coordinateUpper]
  rcases separated with separated | separated |
      separated | separated <;>
    simp_all [min_def, max_def] <;>
    omega

/-- Pointwise containment of two polylines in separated closed rectangles
implies all point/segment and segment/segment rectangle certificates used by
retained-ray rasterization.  No orthogonality hypothesis is needed. -/
theorem
    SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
    {firstLower firstUpper secondLower secondUpper : Cell}
    {first second : List Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle firstLower firstUpper point)
    (secondBounded :
      ∀ point ∈ second,
        InClosedGridRectangle secondLower secondUpper point)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    SourcePolylineRectanglesSeparated first second := by
  constructor
  · intro firstPoint firstPointMember
      secondSegment secondSegmentMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember
    have firstPointBounded :=
      firstBounded firstPoint firstPointMember
    have secondStartBounded :=
      secondBounded secondSegment.start secondEndpoints.1
    have secondFinishBounded :=
      secondBounded secondSegment.finish secondEndpoints.2
    rcases firstLower with ⟨firstLowerX, firstLowerY⟩
    rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
    rcases secondLower with ⟨secondLowerX, secondLowerY⟩
    rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
    rcases firstPoint with ⟨firstX, firstY⟩
    rcases secondSegment with
      ⟨⟨secondStartX, secondStartY⟩,
        ⟨secondFinishX, secondFinishY⟩⟩
    simp only [InClosedGridRectangle]
      at firstPointBounded secondStartBounded secondFinishBounded
    simp only [ClosedGridRectanglesSeparated] at separated ⊢
    simp only [GridSegment.coordinateLower,
      GridSegment.coordinateUpper]
    rcases separated with separated | separated |
        separated | separated <;>
      simp_all [min_def, max_def] <;>
      omega
  · intro firstSegment firstSegmentMember
      secondSegment secondSegmentMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstSegmentMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember
    have firstStartBounded :=
      firstBounded firstSegment.start firstEndpoints.1
    have firstFinishBounded :=
      firstBounded firstSegment.finish firstEndpoints.2
    have secondStartBounded :=
      secondBounded secondSegment.start secondEndpoints.1
    have secondFinishBounded :=
      secondBounded secondSegment.finish secondEndpoints.2
    rcases firstLower with ⟨firstLowerX, firstLowerY⟩
    rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
    rcases secondLower with ⟨secondLowerX, secondLowerY⟩
    rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
    rcases firstSegment with
      ⟨⟨firstStartX, firstStartY⟩,
        ⟨firstFinishX, firstFinishY⟩⟩
    rcases secondSegment with
      ⟨⟨secondStartX, secondStartY⟩,
        ⟨secondFinishX, secondFinishY⟩⟩
    simp only [InClosedGridRectangle]
      at firstStartBounded firstFinishBounded
        secondStartBounded secondFinishBounded
    simp only [ClosedGridRectanglesSeparated] at separated ⊢
    simp only [GridSegment.coordinateLower,
      GridSegment.coordinateUpper]
    rcases separated with separated | separated |
        separated | separated <;>
      simp_all [min_def, max_def] <;>
      omega

/-- Separated enclosing boxes directly supply the mixed retained-terminal
corridor certificate.  The first box need only contain the source prefix,
while the second contains the complete reference route. -/
theorem sourcePrefixCorridorSeparated_of_inSeparatedClosedGridRectangles
    {firstLower firstUpper secondLower secondUpper : Cell}
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourcePrefixBounded :
      ∀ point ∈ sourceRoute.dropLast,
        InClosedGridRectangle firstLower firstUpper point)
    (referenceBounded :
      ∀ point ∈ referenceRoute,
        InClosedGridRectangle secondLower secondUpper point)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  apply
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
      sourceRoute referenceRoute referenceTerminal
      sourceRetained referenceRetained
      sourceLength referenceLength referenceClassified
  exact
    SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
      sourcePrefixBounded referenceBounded separated

/-- For two genuine final retained routes, separated enclosing boxes
discharge the directed source-prefix-versus-complete-fan cross case without
exposing either retained-ray certificates or the intermediate corridor
predicate. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_inSeparatedClosedGridRectangles
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
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
    {sourceRoute referenceRoute : List Cell}
    {sourceIndex referenceIndex : Nat}
    {sourcePoint referenceCenter : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (referenceMember :
      (referenceRoute, referenceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (indicesDifferent : sourceIndex ≠ referenceIndex)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (referenceLast :
      referenceRoute.getLast? = some referenceCenter)
    (sourceNeCenter : sourcePoint ≠ referenceCenter)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    {sourceLower sourceUpper referenceLower referenceUpper : Cell}
    (sourcePrefixBounded :
      ∀ point ∈ sourceRoute.dropLast,
        InClosedGridRectangle sourceLower sourceUpper point)
    (referenceBounded :
      ∀ point ∈ referenceRoute,
        InClosedGridRectangle referenceLower referenceUpper point)
    (boxesSeparated :
      ClosedGridRectanglesSeparated
        sourceLower sourceUpper referenceLower referenceUpper) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor referenceCenter))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  apply
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_sourcePolylineRectanglesSeparated
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      sourceMember referenceMember sourceLength referenceLength
      indicesDifferent sourceHead referenceLast sourceNeCenter
      referenceTerminal referenceSlot referenceClassified
  exact
    SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
      sourcePrefixBounded referenceBounded boxesSeparated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
