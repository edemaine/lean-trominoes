import LeanTrominoes.RetainedAngularFanOuterEscapedSourceSeparation
import LeanTrominoes.RetainedFinalOuterFanSeparation

/-!
# Final shared-head separation for an escaped outer fan

When two final retained routes share their clause endpoint but their source
prefixes are not both singletons, the established planar drawing strictly
separates their discarded terminal rectangles.  The escaped fan obeys the
same radius-288 rectangle bound as an ordinary fan, so the existing final
certificate immediately separates an escaped first fan from an ordinary
second fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Shared clause heads do not obstruct escaped/ordinary outer-fan
separation when the two retained source prefixes are not both singletons. -/
theorem
    retainedFinalEscapedOuterCompleteRoute_strictlyAvoid_ordinary_of_axisAligned_of_not_both_singletonPrefixes
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
    (firstHead : firstRoute.head? = some firstSource)
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (centersDifferent : firstCenter ≠ secondCenter)
    (notBothSingleton :
      ¬(firstRoute.dropLast.length = 1 ∧
        secondRoute.dropLast.length = 1))
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
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor firstTerminal)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
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
  have firstLastD :
      firstRoute.getLastD (0, 0) = firstCenter := by
    simp [List.getLastD_eq_getLast?, firstLast]
  have secondLastD :
      secondRoute.getLastD (0, 0) = secondCenter := by
    simp [List.getLastD_eq_getLast?, secondLast]
  have firstAligned' :
      (⟨polylineLastEntrance firstRoute, firstCenter⟩ :
        GridSegment).IsAxisAligned := by
    rw [← firstLastD]
    exact firstAligned
  have secondAligned' :
      (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
        GridSegment).IsAxisAligned := by
    rw [← secondLastD]
    exact secondAligned
  have rectanglesSeparated :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_finalSegmentRectanglesSeparated_of_axisAligned_of_not_both_singletonPrefixes
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent firstLast secondLast
      headLastNe lastHeadNe lastLastNe notBothSingleton
      firstAligned' secondAligned'
  exact
    retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_ordinary_of_finalSegmentRectanglesSeparated
      factorPositive clearance
      firstRoute secondRoute firstTerminal secondTerminal
      firstSlot secondSlot firstLength secondLength
      firstClassified secondClassified firstEscapeFits
      rectanglesSeparated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
