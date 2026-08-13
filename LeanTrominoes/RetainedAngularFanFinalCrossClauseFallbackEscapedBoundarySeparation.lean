/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackOrder
import LeanTrominoes.RetainedAngularFanFinalStrictEscape
import LeanTrominoes.RetainedAngularFanOuterEscapedCompleteSeparation
import LeanTrominoes.RetainedFinalEscapedSharedCenterSpliceSeparation
import LeanTrominoes.RetainedFinalEscapedOrdinarySharedCenterSpliceSeparation

/-!
# Shared-center escaped fallback boundary separation

The final angular order orients two failed fallback terminals at one
variable center.  Strict scale-four escape room then separates their
complete escaped fans, while the retained positioned drawing separates the
two inherited source prefixes from the opposite fan.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- Pair-valued wrapper around the escaped complete-route separation
theorem, keeping terminal projections opaque in the final drawing proof. -/
private theorem escapedCompleteRoutes_strictlyAvoid_of_order
    (center : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstTerminal.1.angularRank <
        secondTerminal.1.angularRank)
    (firstLengthPositive : 0 < firstTerminal.2)
    (secondLengthPositive : 0 < secondTerminal.2)
    (slotsLt : firstSlot.val < secondSlot.val)
    (firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength firstTerminal)
    (secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength secondTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        center secondTerminal secondSlot) := by
  rcases firstTerminal with ⟨firstDirection, firstLength⟩
  rcases secondTerminal with ⟨secondDirection, secondLength⟩
  exact
    retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection
      firstLength secondLength firstSlot secondSlot
      directionsLt firstLengthPositive secondLengthPositive
      slotsLt firstEscapeStrict secondEscapeStrict

/-- Pair-valued wrapper around mixed escaped/ordinary complete-route
separation. -/
private theorem escapedOrdinaryCompleteRoutes_strictlyAvoid_of_order
    (center : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstTerminal.1.angularRank <
        secondTerminal.1.angularRank)
    (firstLengthPositive : 0 < firstTerminal.2)
    (secondLengthPositive : 0 < secondTerminal.2)
    (secondRadialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val)
    (firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength firstTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        center secondTerminal secondSlot) := by
  rcases firstTerminal with ⟨firstDirection, firstLength⟩
  rcases secondTerminal with ⟨secondDirection, secondLength⟩
  exact
    retainedTerminalFanOuterEscapedOrdinaryCompleteRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection
      firstLength secondLength firstSlot secondSlot
      directionsLt firstLengthPositive secondLengthPositive
      secondRadialPositive slotsLt firstEscapeStrict

/-- Pair-valued wrapper for the reverse angular orientation of the mixed
ordinary/escaped complete-route theorem. -/
private theorem ordinaryEscapedCompleteRoutes_strictlyAvoid_of_order
    (center : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstTerminal.1.angularRank <
        secondTerminal.1.angularRank)
    (firstLengthPositive : 0 < firstTerminal.2)
    (secondLengthPositive : 0 < secondTerminal.2)
    (firstRadialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal)
    (slotsLt : firstSlot.val < secondSlot.val)
    (secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength secondTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        center secondTerminal secondSlot) := by
  rcases firstTerminal with ⟨firstDirection, firstLength⟩
  rcases secondTerminal with ⟨secondDirection, secondLength⟩
  exact
    retainedTerminalFanOuterOrdinaryEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection
      firstLength secondLength firstSlot secondSlot
      directionsLt firstLengthPositive secondLengthPositive
      firstRadialPositive slotsLt secondEscapeStrict

/-- Failed choices in different final source clauses at one variable center
supply both mixed escaped/ordinary and escaped/escaped strict boundary
separation. -/
theorem
    retainedFinalCrossClauseFallbackBoundarySpliceCertificates_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula firstClauseIndex firstLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral
          firstClauseIndex firstLiteralIndex))
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula secondClauseIndex secondLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral
          secondClauseIndex secondLiteralIndex)) ∧
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula firstClauseIndex firstLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral
          firstClauseIndex firstLiteralIndex))
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula secondClauseIndex secondLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral
          secondClauseIndex secondLiteralIndex)) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstRoute :=
    routes firstClauseIndex firstLiteralIndex
  let secondRoute :=
    routes secondClauseIndex secondLiteralIndex
  let firstTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRoute)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRoute)
  let firstScaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstTerminal
  let secondScaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor secondTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let commonCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      placement firstClause firstLiteral
  let scaledFanCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale retainedAngularFanSourceClearanceFactor
        commonCenter)
  have copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        firstClauseMember firstLiteralMember with
    ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        secondClauseMember secondLiteralMember with
    ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
  have routeIndicesDifferent :
      firstRouteIndex ≠ secondRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    simpa using
      congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
  have firstLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstLast :
      firstRoute.getLast? = some commonCenter := by
    simpa [firstRoute, routes, placement, commonCenter] using
      firstEndpoints.2
  have secondLast :
      secondRoute.getLast? = some commonCenter := by
    simpa [secondRoute, routes, placement, commonCenter] using
      secondEndpoints.2.trans
        (congrArg some centersEqual.symm)
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have firstHeadNeLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable inferInstance firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ firstIncidenceMember firstIncidenceMember
  have secondHeadNeLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable inferInstance firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ secondIncidenceMember secondIncidenceMember
  have firstSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ≠ commonCenter := by
    rw [firstEndpoints.1, firstLast] at firstHeadNeLast
    simpa [firstRoute, routes] using firstHeadNeLast
  have secondSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ≠ commonCenter := by
    rw [secondEndpoints.1, secondLast] at secondHeadNeLast
    simpa [secondRoute, routes] using secondHeadNeLast
  have sourcesDifferent :=
    retainedFinalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember clauseIndicesDifferent
  have headsDifferent :
      firstRoute.head? ≠ secondRoute.head? := by
    rw [show firstRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement firstClause) by
          simpa [firstRoute, routes, placement] using firstEndpoints.1,
      show secondRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondClause) by
          simpa [secondRoute, routes, placement] using secondEndpoints.1]
    exact fun equal => sourcesDifferent (Option.some.inj equal)
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal, routes, source] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some secondTerminal := by
    simpa [secondRoute, secondTerminal, routes, source] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstAligned :
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
    simpa [firstRoute, routes, source] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
  have secondAligned :
      (⟨polylineLastEntrance secondRoute,
          secondRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
    simpa [secondRoute, routes, source] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember secondChoiceNone
  have firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength firstScaledTerminal := by
    simpa [firstScaledTerminal, firstTerminal, firstRoute, routes] using
      finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength secondScaledTerminal := by
    simpa [secondScaledTerminal, secondTerminal, secondRoute, routes] using
      finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstScaledLengthPositive :
      0 < firstScaledTerminal.2 := by
    exact
      scaleRetainedTerminalData_length_pos
        retainedAngularFanSourceClearanceFactor_pos
        (by
          simpa [firstTerminal, firstRoute, routes] using
            finalCoordinatedSourceRoute_terminal_length_positive
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty
              firstClauseMember firstLiteralMember)
  have secondScaledLengthPositive :
      0 < secondScaledTerminal.2 := by
    exact
      scaleRetainedTerminalData_length_pos
        retainedAngularFanSourceClearanceFactor_pos
        (by
          simpa [secondTerminal, secondRoute, routes] using
            finalCoordinatedSourceRoute_terminal_length_positive
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty
              secondClauseMember secondLiteralMember)
  have angularOrder :=
    retainedFinalCrossClauseFallbackTerminalAngularOrder_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone
      clauseIndicesDifferent centersEqual
  have secondRadialPositive :
      0 < retainedTerminalFanOuterRadialLength secondScaledTerminal := by
    have escapePositive :
        0 < retainedTerminalFanOuterSourceEscapeLength := by
      native_decide
    omega
  have mixedFansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          scaledFanCenter firstScaledTerminal firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          scaledFanCenter secondScaledTerminal secondSlot) := by
    rcases angularOrder with firstBefore | secondBefore
    · exact
        escapedOrdinaryCompleteRoutes_strictlyAvoid_of_order
          scaledFanCenter firstScaledTerminal secondScaledTerminal
          firstSlot secondSlot
          (by
            simpa [firstScaledTerminal, secondScaledTerminal,
              firstTerminal, secondTerminal, firstRoute, secondRoute,
              routes, firstSlot, secondSlot] using firstBefore.2)
          firstScaledLengthPositive secondScaledLengthPositive
          secondRadialPositive
          (by simpa [firstSlot, secondSlot] using firstBefore.1)
          firstEscapeStrict
    · exact
        (ordinaryEscapedCompleteRoutes_strictlyAvoid_of_order
          scaledFanCenter secondScaledTerminal firstScaledTerminal
          secondSlot firstSlot
          (by
            simpa [firstScaledTerminal, secondScaledTerminal,
              firstTerminal, secondTerminal, firstRoute, secondRoute,
              routes, firstSlot, secondSlot] using secondBefore.2)
          secondScaledLengthPositive firstScaledLengthPositive
          secondRadialPositive
          (by simpa [firstSlot, secondSlot] using secondBefore.1)
          firstEscapeStrict).symm
  have fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          scaledFanCenter firstScaledTerminal firstSlot)
        (retainedTerminalFanOuterEscapedCompleteRoute
          scaledFanCenter secondScaledTerminal secondSlot) := by
    rcases angularOrder with firstBefore | secondBefore
    · exact
        escapedCompleteRoutes_strictlyAvoid_of_order
          scaledFanCenter firstScaledTerminal secondScaledTerminal
          firstSlot secondSlot
          (by
            simpa [firstScaledTerminal, secondScaledTerminal,
              firstTerminal, secondTerminal, firstRoute, secondRoute,
              routes, firstSlot, secondSlot] using firstBefore.2)
          firstScaledLengthPositive secondScaledLengthPositive
          (by simpa [firstSlot, secondSlot] using firstBefore.1)
          firstEscapeStrict secondEscapeStrict
    · exact
        (escapedCompleteRoutes_strictlyAvoid_of_order
          scaledFanCenter secondScaledTerminal firstScaledTerminal
          secondSlot firstSlot
          (by
            simpa [firstScaledTerminal, secondScaledTerminal,
              firstTerminal, secondTerminal, firstRoute, secondRoute,
              routes, firstSlot, secondSlot] using secondBefore.2)
          secondScaledLengthPositive firstScaledLengthPositive
          (by simpa [firstSlot, secondSlot] using secondBefore.1)
          secondEscapeStrict firstEscapeStrict).symm
  constructor
  · simpa [firstRoute, secondRoute, firstTerminal, secondTerminal,
      firstScaledTerminal, secondScaledTerminal, firstSlot, secondSlot,
      routes, source, placement, commonCenter, scaledFanCenter] using
      retainedFinalSourceScaledEscapedOrdinarySplicedBoundaryPolylines_strictlyAvoid_of_axisAligned_of_fansAvoid
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        retainedAngularFanSourceClearanceFactor_gt_one
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent headsDifferent
        (by simpa [firstRoute, routes, placement] using firstEndpoints.1)
        (by simpa [secondRoute, routes, placement] using secondEndpoints.1)
        firstLast secondLast
        firstSourceNeCenter secondSourceNeCenter
        firstAligned secondAligned
        firstTerminal secondTerminal firstSlot secondSlot
        firstClassified secondClassified
        (Nat.le_of_lt firstEscapeStrict)
        mixedFansAvoid
  · simpa [firstRoute, secondRoute, firstTerminal, secondTerminal,
      firstScaledTerminal, secondScaledTerminal, firstSlot, secondSlot,
      routes, source, placement, commonCenter, scaledFanCenter] using
      retainedFinalSourceScaledEscapedSplicedBoundaryPolylines_strictlyAvoid_of_axisAligned_of_fansAvoid
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        retainedAngularFanSourceClearanceFactor_gt_one
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent headsDifferent
        (by simpa [firstRoute, routes, placement] using firstEndpoints.1)
        (by simpa [secondRoute, routes, placement] using secondEndpoints.1)
        firstLast secondLast
        firstSourceNeCenter secondSourceNeCenter
        firstAligned secondAligned
        firstTerminal secondTerminal firstSlot secondSlot
        firstClassified secondClassified
        (Nat.le_of_lt firstEscapeStrict)
        (Nat.le_of_lt secondEscapeStrict)
        fansAvoid

end PeriodicOrthocrossing
end LeanTrominoes
