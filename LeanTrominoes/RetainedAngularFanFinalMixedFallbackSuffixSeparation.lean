/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackEscapedSuffixSeparation

/-!
# Selected fallback boundaries avoid cross-clause suffixes

The final coordinated router uses an ordinary fallback boundary unless the
raw source prefix is a singleton, in which case it uses the delayed-lane
escaped boundary.  Existing geometry separates both choices from every
other clause's Figure 7 suffix; this file packages the router's case split
as one theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- The source-to-Figure-7-boundary prefix selected by the final router when
the checked direct-source choice fails. -/
def retainedFinalCoordinatedFallbackBoundaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) : List Cell :=
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute))
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  if rawRoute.dropLast.length = 1 then
    retainedAngularFanEscapedSplicedBoundaryRoute
      route terminal slot
  else
    retainedAngularFanSplicedBoundaryRoute
      route terminal slot

/-- Whichever fallback boundary the final router selects reaches exactly the
head of its unchanged Figure 7 suffix. -/
theorem retainedFinalCoordinatedFallbackBoundaryPrefix_boundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
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
    let suffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)
    (retainedFinalCoordinatedFallbackBoundaryPrefix
      formula literal clauseIndex literalIndex).getLast? =
        suffix.head? := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have escapedBoundary :=
    retainedFinalEscapedFallbackOccurrenceRoute_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix, if_pos]
    simpa [rawRoute, rawTerminal, route, terminal, slot] using
      escapedBoundary
  · have routeLength : 2 ≤ route.length := by
      simpa [route, rawRoute] using
        finalCoordinatedScaledSourceRoute_length_ge_two
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember
    have routeClassified :
        retainedTerminalDirectionClassify
            (routeTerminalVector route) =
          some terminal := by
      simpa [route, terminal, rawRoute, rawTerminal] using
        finalCoordinatedScaledSourceRoute_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember
    have routeRetained : RetainedRayPolyline route := by
      simpa [route, rawRoute] using
        finalCoordinatedScaledSourceRoute_retainedRay
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember
    have routeHead :=
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    have ordinaryValid :=
      retainedAngularFanSplicedBoundaryRoute_valid
        route terminal slot routeLength routeClassified routeRetained
        (by simpa [route, rawRoute] using routeHead)
    have escapedValid :=
      retainedFinalEscapedFallbackBoundaryPrefix_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    have ordinaryToEscaped :
        (retainedAngularFanSplicedBoundaryRoute
            route terminal slot).getLast? =
          (retainedAngularFanEscapedSplicedBoundaryRoute
            route terminal slot).getLast? := by
      exact ordinaryValid.2.1.trans
        (by
          simpa [rawRoute, rawTerminal, route, terminal, slot] using
            escapedValid.2.1.symm)
    have ordinaryBoundary :
        (retainedAngularFanSplicedBoundaryRoute
            route terminal slot).getLast? =
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix
              ((finalCoordinatedPlacement formula).scale
                retainedAngularFanSourceClearanceFactor)
              (angularOccurrenceOrder
                ((finalCoordinatedSource formula).scale
                  retainedAngularFanSourceClearanceFactor).erase
                (PositionedPeriodicCNF.scaleIncidenceRoutes
                  retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes formula)))
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal clauseIndex literalIndex)).head? := by
      exact ordinaryToEscaped.trans
        (by
          simpa [rawRoute, rawTerminal, route, terminal, slot] using
            escapedBoundary)
    rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix]
    exact ordinaryBoundary

/-- A selected failed-choice fallback boundary is contact-free from the
Figure 7 suffix of every genuine incidence in a different final source
clause. -/
theorem
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_crossClauseOccurrenceSuffix
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
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
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
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula firstLiteral firstClauseIndex firstLiteralIndex)
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
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (secondClause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  have firstRouteLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have firstRouteClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have firstRawOrthogonal :
      OrthogonalPolyline firstRawRoute := by
    simpa [firstRawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        firstChoiceNone
  have firstRouteOrthogonal : OrthogonalPolyline firstRoute := by
    simpa [firstRoute] using
      firstRawOrthogonal.scalePolyline
        retainedAngularFanSourceClearanceFactor_pos
  have ordinaryPolylineOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      firstRoute firstTerminal firstSlot
      firstRouteLength firstRouteClassified firstRouteOrthogonal
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength firstTerminal := by
    simpa [firstTerminal, firstRawTerminal, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have escapedPolylineOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      firstRoute firstTerminal firstSlot
      firstRouteLength firstRouteClassified firstRouteOrthogonal
      escapeFits
  have separated :=
    retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone clauseIndicesDifferent
  by_cases singletonPrefix : firstRawRoute.dropLast.length = 1
  · by_cases centersEqual :
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            firstClause firstLiteral =
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral
    · have escapedAvoid :=
        retainedFinalCrossClauseEscapedBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter_of_singletonPrefix
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          clauseIndicesDifferent centersEqual
          (by simpa [firstRawRoute] using singletonPrefix)
      rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
      simp only [firstRawRoute, singletonPrefix, if_pos]
      rw [retainedAngularFanEscapedSplicedBoundaryRoute,
        rasterizeRetainedPolyline_eq_of_orthogonal
          escapedPolylineOrthogonal]
      simpa [source, placement, routes, order,
        firstRawRoute, firstRawTerminal, firstRoute,
        firstTerminal, firstSlot, secondSuffix] using escapedAvoid
    · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
      simp only [firstRawRoute, singletonPrefix, if_pos]
      rw [retainedAngularFanEscapedSplicedBoundaryRoute,
        rasterizeRetainedPolyline_eq_of_orthogonal
          escapedPolylineOrthogonal]
      simpa [source, placement, routes, order,
        firstRawRoute, firstRawTerminal, firstRoute,
        firstTerminal, firstSlot, secondSuffix] using
        separated.2 centersEqual
  · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [firstRawRoute, singletonPrefix]
    rw [retainedAngularFanSplicedBoundaryRoute,
      rasterizeRetainedPolyline_eq_of_orthogonal
        ordinaryPolylineOrthogonal]
    simpa [source, placement, routes, order,
      firstRawRoute, firstRawTerminal, firstRoute,
      firstTerminal, firstSlot, secondSuffix] using separated.1

end PeriodicOrthocrossing
end LeanTrominoes
