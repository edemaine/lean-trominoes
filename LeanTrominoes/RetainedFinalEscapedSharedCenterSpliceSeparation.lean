import LeanTrominoes.RetainedFinalEscapedSourceScaledSpliceSeparation

/-!
# Escaped source splices with externally separated fans

The final retained source geometry separates the inherited source prefixes
from each other's escaped outer fans without requiring distinct variable
centers.  Thus an external escaped-fan separation certificate is enough to
assemble the two complete escaped boundary splices.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- Two source-scaled escaped splices are strictly separated when their
discarded final segments are axis-aligned and their complete escaped fans
are strictly separated.  The two source routes may share their endpoint. -/
theorem
    retainedFinalSourceScaledEscapedSplicedBoundaryPolylines_strictlyAvoid_of_axisAligned_of_fansAvoid
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
          (scaleRetainedTerminalData factor firstTerminal))
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor secondTerminal))
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale factor firstCenter))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale factor secondCenter))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have sourcePrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstRoute.dropLast secondRoute.dropLast :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  have scaledSourcePrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline factor firstRoute).dropLast
        (scalePolyline factor secondRoute).dropLast := by
    have scaled :=
      sourcePrefixesAvoid.scalePolyline
        (factor := (factor : Int))
        (by exact_mod_cast Nat.zero_lt_of_lt factorGreaterThanOne)
    simpa [scalePolyline] using scaled
  have firstPrefixAvoidSecondEscaped :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterEscapedCompleteRoute_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      firstSourceNeSecondCenter
      secondTerminal secondSlot secondClassified secondEscapeFits
      (by
        have secondLastD :
            secondRoute.getLastD (0, 0) = secondCenter := by
          simp [List.getLastD_eq_getLast?, secondLast]
        rw [← secondLastD]
        exact secondAligned)
  have secondPrefixAvoidFirstEscaped :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterEscapedCompleteRoute_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne
      secondMember firstMember secondLength firstLength
      (Ne.symm indicesDifferent) (Ne.symm headsDifferent)
      secondHead firstLast secondSourceNeFirstCenter
      firstTerminal firstSlot firstClassified firstEscapeFits
      (by
        have firstLastD :
            firstRoute.getLastD (0, 0) = firstCenter := by
          simp [List.getLastD_eq_getLast?, firstLast]
        rw [← firstLastD]
        exact firstAligned)
  have firstScaledLength :
      2 ≤ (scalePolyline factor firstRoute).length := by
    simpa [scalePolyline] using firstLength
  have secondScaledLength :
      2 ≤ (scalePolyline factor secondRoute).length := by
    simpa [scalePolyline] using secondLength
  have firstScaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector
            (scalePolyline factor firstRoute)) =
        some (scaleRetainedTerminalData factor firstTerminal) := by
    simpa using
      routeTerminalVector_scale_classified
        (Nat.zero_lt_of_lt factorGreaterThanOne) firstClassified
  have secondScaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector
            (scalePolyline factor secondRoute)) =
        some (scaleRetainedTerminalData factor secondTerminal) := by
    simpa using
      routeTerminalVector_scale_classified
        (Nat.zero_lt_of_lt factorGreaterThanOne) secondClassified
  exact
    retainedAngularFanEscapedSplicedBoundaryPolylines_strictlyAvoid
      (scalePolyline factor firstRoute)
      (scalePolyline factor secondRoute)
      (scaleRetainedTerminalData factor firstTerminal)
      (scaleRetainedTerminalData factor secondTerminal)
      firstSlot secondSlot
      firstScaledLength secondScaledLength
      firstScaledClassified secondScaledClassified
      scaledSourcePrefixesAvoid
      (by
        simpa [List.getLastD_eq_getLast?, secondLast,
          scalePolyline_getLastD] using firstPrefixAvoidSecondEscaped)
      (by
        simpa [List.getLastD_eq_getLast?, firstLast,
          scalePolyline_getLastD] using
          secondPrefixAvoidFirstEscaped.symm)
      (by
        simpa [List.getLastD_eq_getLast?, firstLast, secondLast,
          scalePolyline_getLastD] using fansAvoid)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
