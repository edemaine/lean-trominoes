/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackSuffixSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedSpokeSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSingletonSplice

/-!
# Singleton escaped fallback boundaries avoid shared-center suffixes

A singleton-prefix escaped boundary splice is exactly its complete escaped
outer fan.  At a shared variable center that fan avoids every other
occurrence's Figure 7 spoke, which is the positioned occurrence suffix.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- Normalize a singleton escaped splice at a separately named final
point, avoiding large final-drawing reductions at the call site. -/
private theorem escapedSplice_eq_outerCompleteRoute_at_finalPoint
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (singletonPrefix : route.dropLast.length = 1)
    (routeLastD : route.getLastD (0, 0) = finalPoint) :
    retainedAngularFanEscapedSplicedBoundaryPolyline
        route terminal slot =
      retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        terminal slot := by
  rw [← routeLastD]
  exact
    retainedAngularFanEscapedSplicedBoundaryPolyline_eq_outerCompleteRoute_of_singletonPrefix
      route terminal slot routeLength classified singletonPrefix

/-- A singleton-prefix escaped boundary splice of one final incidence
strictly avoids the Figure 7 suffix of an incidence in a different clause
at the same variable center. -/
theorem
    retainedFinalCrossClauseEscapedBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter_of_singletonPrefix
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
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)
    (singletonPrefix :
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast.length = 1) :
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
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let firstRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        firstRawRoute
    let firstTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (classifiedRetainedTerminalData
          (routeTerminalVector firstRawRoute))
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral
        firstClauseIndex firstLiteralIndex
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (secondClause.scale
            retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        firstRoute firstTerminal firstSlot)
      secondSuffix := by
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
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRawRoute
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstRawTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstFinalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        firstClause firstLiteral)
  let secondFinalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        secondClause secondLiteral)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement firstFinalPoint
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (secondClause.scale
          retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  have finalPointsEqual :
      firstFinalPoint = secondFinalPoint := by
    exact congrArg
      (Cell.scale retainedAngularFanSourceClearanceFactor)
      centersEqual
  have refinedCentersEqual :
      Cell.scale retainedTerminalFanTotalRefinement firstFinalPoint =
        Cell.scale retainedTerminalFanTotalRefinement secondFinalPoint :=
    congrArg
      (Cell.scale retainedTerminalFanTotalRefinement)
      finalPointsEqual
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCrossClauseCoordinatedOccurrenceSlots_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
  have routeLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have routeFinal :
      firstRoute.getLast? = some firstFinalPoint := by
    simpa [firstRoute, firstRawRoute, firstFinalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have scaledSingletonPrefix :
      firstRoute.dropLast.length = 1 := by
    simpa [firstRoute, firstRawRoute, scalePolyline] using singletonPrefix
  have firstLastD :
      firstRoute.getLastD (0, 0) = firstFinalPoint := by
    simp [List.getLastD_eq_getLast?, routeFinal]
  have boundaryEqual :
      retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot =
        retainedTerminalFanOuterEscapedCompleteRoute
          center firstTerminal firstSlot := by
    change
      retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot =
        retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            firstFinalPoint)
          firstTerminal firstSlot
    exact
      escapedSplice_eq_outerCompleteRoute_at_finalPoint
        firstRoute firstTerminal firstSlot firstFinalPoint
        routeLength classified scaledSingletonPrefix firstLastD
  have terminalLengthPositive : 0 < firstTerminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength firstTerminal := by
    simpa [firstTerminal, firstRawTerminal, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center secondSlot =
        secondSuffix := by
    rw [show center =
        Cell.scale retainedTerminalFanTotalRefinement
          secondFinalPoint by
      exact refinedCentersEqual]
    simpa [source, placement, routes, order,
      secondFinalPoint, secondSlot, secondSuffix] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  rw [boundaryEqual]
  change
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center firstTerminal firstSlot)
      secondSuffix
  rw [← spokeEqual]
  exact
    retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
      center firstTerminal firstSlot secondSlot
      terminalLengthPositive escapeFits slotsDifferent

end PeriodicOrthocrossing
end LeanTrominoes
