/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackEscapedBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackEscapedSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackOccurrenceSeparation

/-!
# Shared-center explicit fallback occurrence separation

The shared-center boundary certificates and directed boundary/suffix
certificates assemble across the validated fan-boundary joins.  A singleton
first prefix gives escaped/ordinary separation; if the second prefix is also
singleton, the same assembly gives escaped/escaped separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- At one variable center, a singleton escaped fallback occurrence avoids
an ordinary fallback occurrence from another clause; a second singleton
hypothesis upgrades the latter to an escaped fallback as well. -/
theorem
    retainedFinalCrossClauseFallbackExplicitOccurrenceRouteCertificates_of_sameCenter
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
    (firstSingletonPrefix :
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast.length = 1)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let order := angularOccurrenceOrder source.erase routes
    let firstScaledClause :=
      firstClause.scale retainedAngularFanSourceClearanceFactor
    let secondScaledClause :=
      secondClause.scale retainedAngularFanSourceClearanceFactor
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let secondRawRoute :=
      finalCoordinatedSourceRoutes
        formula secondClauseIndex secondLiteralIndex
    let firstRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector firstRawRoute)
    let secondRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector secondRawRoute)
    let firstRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        firstRawRoute
    let secondRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        secondRawRoute
    let firstTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor firstRawTerminal
    let secondTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor secondRawTerminal
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    let firstEscapedPrefix :=
      retainedAngularFanEscapedSplicedBoundaryRoute
        firstRoute firstTerminal firstSlot
    let secondPrefix :=
      retainedAngularFanSplicedBoundaryRoute
        secondRoute secondTerminal secondSlot
    let secondEscapedPrefix :=
      retainedAngularFanEscapedSplicedBoundaryRoute
        secondRoute secondTerminal secondSlot
    let firstSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          firstScaledClause firstLiteral
          firstClauseIndex firstLiteralIndex)
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          secondScaledClause secondLiteral
          secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
        (joinAtEndpoint firstEscapedPrefix firstSuffix)
        (joinAtEndpoint secondPrefix secondSuffix) ∧
      ((finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex).dropLast.length = 1 →
        RoutesStrictlyAvoidEachOther
          (joinAtEndpoint firstEscapedPrefix firstSuffix)
          (joinAtEndpoint secondEscapedPrefix secondSuffix)) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  let firstScaledClause :=
    firstClause.scale retainedAngularFanSourceClearanceFactor
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let secondRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRawRoute)
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor firstRawRoute
  let secondRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor secondRawRoute
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstRawTerminal
  let secondTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor secondRawTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstEscapedPrefix :=
    retainedAngularFanEscapedSplicedBoundaryRoute
      firstRoute firstTerminal firstSlot
  let secondPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      secondRoute secondTerminal secondSlot
  let secondEscapedPrefix :=
    retainedAngularFanEscapedSplicedBoundaryRoute
      secondRoute secondTerminal secondSlot
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        firstScaledClause firstLiteral
        firstClauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  let firstMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset firstScaledClause firstLiteral)
        (angularOccurrenceIndex order
          firstLiteral firstClauseIndex firstLiteralIndex))
  let secondMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset secondScaledClause secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex))
  have firstLength : 2 ≤ firstRawRoute.length := by
    simpa [firstRawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRawRoute.length := by
    simpa [secondRawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstRouteLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, scalePolyline] using firstLength
  have secondRouteLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute, scalePolyline] using secondLength
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) = some firstTerminal := by
    simpa [firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) = some secondTerminal := by
    simpa [secondRoute, secondTerminal,
      secondRawRoute, secondRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstRawOrthogonal : OrthogonalPolyline firstRawRoute := by
    simpa [firstRawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
  have secondRawOrthogonal : OrthogonalPolyline secondRawRoute := by
    simpa [secondRawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember secondChoiceNone
  have firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength firstTerminal := by
    simpa [firstTerminal, firstRawTerminal, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength secondTerminal := by
    simpa [secondTerminal, secondRawTerminal, secondRawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstEscapedOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      firstRoute firstTerminal firstSlot
      firstRouteLength firstClassified
      (by
        simpa [firstRoute] using
          firstRawOrthogonal.scalePolyline
            retainedAngularFanSourceClearanceFactor_pos)
      firstEscapeFits
  have secondOrdinaryOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      secondRoute secondTerminal secondSlot
      secondRouteLength secondClassified
      (by
        simpa [secondRoute] using
          secondRawOrthogonal.scalePolyline
            retainedAngularFanSourceClearanceFactor_pos)
  have secondEscapedOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      secondRoute secondTerminal secondSlot
      secondRouteLength secondClassified
      (by
        simpa [secondRoute] using
          secondRawOrthogonal.scalePolyline
            retainedAngularFanSourceClearanceFactor_pos)
      secondEscapeFits
  have firstEscapedPrefixEq :
      firstEscapedPrefix =
        retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot := by
    exact rasterizeRetainedPolyline_eq_of_orthogonal
      firstEscapedOrthogonal
  have secondPrefixEq :
      secondPrefix =
        retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot := by
    exact rasterizeRetainedPolyline_eq_of_orthogonal
      secondOrdinaryOrthogonal
  have secondEscapedPrefixEq :
      secondEscapedPrefix =
        retainedAngularFanEscapedSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot := by
    exact rasterizeRetainedPolyline_eq_of_orthogonal
      secondEscapedOrthogonal
  have boundaryCertificates :=
    retainedFinalCrossClauseFallbackBoundarySpliceCertificates_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone
      clauseIndicesDifferent centersEqual
  have mixedPrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstEscapedPrefix secondPrefix := by
    rw [firstEscapedPrefixEq, secondPrefixEq]
    simpa [firstRoute, secondRoute, firstTerminal, secondTerminal,
      firstRawRoute, secondRawRoute,
      firstRawTerminal, secondRawTerminal,
      firstSlot, secondSlot] using boundaryCertificates.1
  have escapedPrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstEscapedPrefix secondEscapedPrefix := by
    rw [firstEscapedPrefixEq, secondEscapedPrefixEq]
    simpa [firstRoute, secondRoute, firstTerminal, secondTerminal,
      firstRawRoute, secondRawRoute,
      firstRawTerminal, secondRawTerminal,
      firstSlot, secondSlot] using boundaryCertificates.2
  have firstPrefixAvoidsSecondSuffix :
      RoutesStrictlyAvoidEachOther
        firstEscapedPrefix secondSuffix := by
    rw [firstEscapedPrefixEq]
    simpa [source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal, firstSlot,
      secondSuffix] using
      retainedFinalCrossClauseEscapedBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter_of_singletonPrefix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual firstSingletonPrefix
  have firstSuffixAvoidsSecondPrefix :
      RoutesStrictlyAvoidEachOther firstSuffix secondPrefix := by
    rw [secondPrefixEq]
    simpa [source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      secondRoute, secondTerminal,
      secondRawRoute, secondRawTerminal, secondSlot,
      firstSuffix] using
      (retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember firstClauseMember
        secondLiteralMember firstLiteralMember
        (Ne.symm clauseIndicesDifferent) centersEqual.symm).symm
  have suffixesAvoid :
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix := by
    simpa [source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      firstSuffix, secondSuffix] using
      retainedFinalCrossClauseOccurrenceSuffixes_strictlyAvoid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember clauseIndicesDifferent
  have firstBoundary :
      firstEscapedPrefix.getLast? = firstSuffix.head? := by
    simpa [source, placement, routes, order,
      firstScaledClause, firstRawRoute, firstRawTerminal,
      firstSlot, firstRoute, firstTerminal,
      firstEscapedPrefix, firstSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapedBoundary :
      secondEscapedPrefix.getLast? = secondSuffix.head? := by
    simpa [source, placement, routes, order,
      secondScaledClause, secondRawRoute, secondRawTerminal,
      secondSlot, secondRoute, secondTerminal,
      secondEscapedPrefix, secondSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have secondOrdinaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      secondRoute secondTerminal secondSlot
      secondRouteLength secondClassified
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_retainedRay
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            secondClauseMember secondLiteralMember)
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_head
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            secondClauseMember secondLiteralMember)
  have secondEscapedValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have secondBoundary :
      secondPrefix.getLast? = secondSuffix.head? := by
    calc
      secondPrefix.getLast? =
          secondEscapedPrefix.getLast? := by
        exact secondOrdinaryValid.2.1.trans
          (by
            simpa [secondRawRoute, secondRawTerminal,
              secondSlot, secondRoute, secondTerminal,
              secondEscapedPrefix] using
              secondEscapedValid.2.1.symm)
      _ = secondSuffix.head? := secondEscapedBoundary
  have firstSuffixHead :
      firstSuffix.head? = some firstMiddle := by
    simp [firstSuffix, firstMiddle, scalePolyline]
  have secondSuffixHead :
      secondSuffix.head? = some secondMiddle := by
    simp [secondSuffix, secondMiddle, scalePolyline]
  have joinSeparated
      (leftPrefix rightPrefix : List Cell)
      (prefixesSeparated :
        RoutesStrictlyAvoidEachOther leftPrefix rightPrefix)
      (leftPrefixAvoidsRightSuffix :
        RoutesStrictlyAvoidEachOther leftPrefix secondSuffix)
      (leftSuffixAvoidsRightPrefix :
        RoutesStrictlyAvoidEachOther firstSuffix rightPrefix)
      (leftBoundary :
        leftPrefix.getLast? = some firstMiddle)
      (rightBoundary :
        rightPrefix.getLast? = some secondMiddle) :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint leftPrefix firstSuffix)
        (joinAtEndpoint rightPrefix secondSuffix) := by
    have leftPrefixAvoidsRightComplete :=
      prefixesSeparated.join_right
        leftPrefixAvoidsRightSuffix
        rightBoundary secondSuffixHead
    have leftSuffixAvoidsRightComplete :=
      leftSuffixAvoidsRightPrefix.join_right
        suffixesAvoid rightBoundary secondSuffixHead
    exact
      leftPrefixAvoidsRightComplete.join_left
        leftSuffixAvoidsRightComplete
        leftBoundary firstSuffixHead
  constructor
  · exact
      joinSeparated firstEscapedPrefix secondPrefix
        mixedPrefixesAvoid firstPrefixAvoidsSecondSuffix
        firstSuffixAvoidsSecondPrefix
        (firstBoundary.trans firstSuffixHead)
        (secondBoundary.trans secondSuffixHead)
  · intro secondSingletonPrefix
    have firstSuffixAvoidsSecondEscapedPrefix :
        RoutesStrictlyAvoidEachOther
          firstSuffix secondEscapedPrefix := by
      rw [secondEscapedPrefixEq]
      simpa [source, placement, routes, order,
        firstScaledClause, secondScaledClause,
        secondRoute, secondTerminal,
        secondRawRoute, secondRawTerminal, secondSlot,
        firstSuffix] using
        (retainedFinalCrossClauseEscapedBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter_of_singletonPrefix
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondClauseMember firstClauseMember
          secondLiteralMember firstLiteralMember
          (Ne.symm clauseIndicesDifferent) centersEqual.symm
          secondSingletonPrefix).symm
    exact
      joinSeparated firstEscapedPrefix secondEscapedPrefix
        escapedPrefixesAvoid firstPrefixAvoidsSecondSuffix
        firstSuffixAvoidsSecondEscapedPrefix
        (firstBoundary.trans firstSuffixHead)
        (secondEscapedBoundary.trans secondSuffixHead)

end PeriodicOrthocrossing
end LeanTrominoes
