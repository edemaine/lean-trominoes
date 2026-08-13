/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceEscapedSplicePointSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSpliceSeparation
import LeanTrominoes.RetainedAngularFanSourceRadialSeparation
import LeanTrominoes.RetainedFinalEscapedOuterFanSeparation

/-!
# Distinct-endpoint separation for escaped source splices

Retained source planarity separates an escaped replacement fan from every
other source prefix when their advertised endpoints differ.  Together with
the final-segment rectangle certificates for escaped fan pairs, this closes
escaped/ordinary and escaped/escaped boundary-splice separation at distinct
variable centers.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- The retained drawing's final-segment certificate supplies the
axis-aligned separation hypotheses for a source prefix and another route's
complete escaped fan. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterEscapedCompleteRoute_of_axisAligned
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
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor secondTerminal))
    (secondFinalSegmentAligned :
      (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
        GridSegment).IsAxisAligned) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast
      (retainedTerminalFanOuterEscapedCompleteRoute
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
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerEscapedCompleteRoute_of_axisAligned
      factorGreaterThanOne
      firstRoute secondRoute secondTerminal secondSlot
      secondLength secondClassified secondEscapeFits
      secondFinalSegmentAligned sourceAvoids
  rw [scalePolyline_getLastD, secondLastD] at separated
  exact separated

/-- At distinct endpoint pairs, one escaped and one ordinary source splice
are strictly separated after source-first refinement. -/
theorem
    retainedFinalSourceScaledEscapedOrdinarySplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
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
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor firstTerminal)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
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
  have firstPrefixAvoidSecondFan :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      firstSourceNeSecondCenter
      secondTerminal secondSlot secondClassified
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
  have fansAvoid :=
    retainedFinalEscapedOuterCompleteRoute_strictlyAvoid_ordinary_of_distinctEndpoints_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      (Nat.zero_lt_of_lt factorGreaterThanOne) clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
      firstHead secondHead firstLast secondLast
      firstSourceNeSecondCenter secondSourceNeFirstCenter
      centersDifferent firstAligned secondAligned
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified firstEscapeFits
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
    retainedAngularFanEscapedOrdinarySplicedBoundaryPolylines_strictlyAvoid
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
          scalePolyline_getLastD] using firstPrefixAvoidSecondFan)
      (by
        simpa [List.getLastD_eq_getLast?, firstLast,
          scalePolyline_getLastD] using
          secondPrefixAvoidFirstEscaped.symm)
      (by
        simpa [List.getLastD_eq_getLast?, firstLast, secondLast,
          scalePolyline_getLastD] using fansAvoid)

/-- At distinct endpoint pairs, two escaped source splices are strictly
separated after source-first refinement. -/
theorem
    retainedFinalSourceScaledEscapedSplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
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
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor firstTerminal))
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor secondTerminal)) :
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
  have fansAvoid :=
    retainedFinalEscapedOuterCompleteRoutes_strictlyAvoid_of_distinctEndpoints_of_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      (Nat.zero_lt_of_lt factorGreaterThanOne) clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
      firstHead secondHead firstLast secondLast
      firstSourceNeSecondCenter secondSourceNeFirstCenter
      centersDifferent firstAligned secondAligned
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified
      firstEscapeFits secondEscapeFits
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
