import LeanTrominoes.RetainedAngularFanOuterSourceSeparation
import LeanTrominoes.RetainedFinalFlatNormalizedCorridorSeparation
import LeanTrominoes.RetainedFinalRoutePrefixRectangleSeparation

/-!
# Final outer-fan separation inherited from retained route planarity

When two final retained routes have different advertised endpoints and both
discarded terminal segments are axis-aligned, continuous planarity separates
their integral terminal rectangles.  Source refinement then separates the
two complete outer fans, and the unconditional directed cross theorem closes
separation of the full source-to-boundary splices.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Different endpoint pairs and axis-aligned final segments of two final
retained routes give strictly separated complete outer fans. -/
theorem
    retainedFinalOuterCompleteRoutes_strictlyAvoid_of_axisAligned
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
    {factor : Nat} (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource firstCenter secondCenter : Cell}
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
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (centersDifferent : firstCenter ≠ secondCenter)
    (firstAligned :
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance secondRoute,
          secondRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor firstRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor secondRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have headLastNe :
      firstRoute.head? ≠ secondRoute.getLast? := by
    rw [firstHead, secondLast]
    exact fun equal =>
      firstSourceNeSecondCenter (Option.some.inj equal)
  have lastHeadNe :
      firstRoute.getLast? ≠ secondRoute.head? := by
    rw [firstLast, secondHead]
    exact fun equal =>
      secondSourceNeFirstCenter (Option.some.inj equal.symm)
  have lastLastNe :
      firstRoute.getLast? ≠ secondRoute.getLast? := by
    rw [firstLast, secondLast]
    exact fun equal =>
      centersDifferent (Option.some.inj equal)
  have rectanglesSeparated :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_finalSegmentRectanglesSeparated_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent headLastNe lastHeadNe lastLastNe
      firstAligned secondAligned
  exact
    retainedTerminalFanOuterCompleteRoutes_strictlyAvoid_of_finalSegmentRectanglesSeparated
      factorPositive clearance
      firstRoute secondRoute firstTerminal secondTerminal
      firstSlot secondSlot firstLength secondLength
      firstClassified secondClassified rectanglesSeparated

/-- In the axis-aligned, endpoint-distinct class, final retained planarity
unconditionally separates both selected outer fans and hence the two full
source-to-boundary splices. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
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
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource firstCenter secondCenter : Cell}
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
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (centersDifferent : firstCenter ≠ secondCenter)
    (firstAligned :
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance secondRoute,
          secondRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have fansAvoid :=
    retainedFinalOuterCompleteRoutes_strictlyAvoid_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne.le
      (by omega)
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
      firstHead secondHead firstLast secondLast
      firstSourceNeSecondCenter secondSourceNeFirstCenter
      centersDifferent firstAligned secondAligned
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified
  exact
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
      firstHead secondHead firstLast secondLast
      firstSourceNeSecondCenter secondSourceNeFirstCenter
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified fansAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
