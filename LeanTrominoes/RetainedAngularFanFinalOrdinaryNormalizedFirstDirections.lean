/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOrdinaryFigure7HeadIsolation
import LeanTrominoes.RetainedAngularFanFinalOrdinaryFigure7Identification
import LeanTrominoes.RetainedAngularFanOrdinaryFigure7NormalizedFirstDirections

/-! # Normalized first directions of final ordinary fallbacks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 500000

/-- A genuine non-singleton failed-direct occurrence exposes the first
direction of its source-clearance-scaled route even after final loop erasure. -/
theorem
    retainedFinalOrdinaryFallbackOccurrenceRoute_normalized_firstDirection
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (prefixLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length ≠ 1) :
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFinalOrdinaryFallbackOccurrenceRoute
            formula clause literal clauseIndex literalIndex)) =
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) := by
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let routeSourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause)
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawLengthNe : rawRoute.length ≠ 2 := by
    intro lengthEq
    apply prefixLengthNe
    simp [rawRoute, List.length_dropLast, lengthEq]
  have routeLength : 3 ≤ route.length := by
    simpa [route, scalePolyline] using
      (show 3 ≤ rawRoute.length by omega)
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) = some terminal := by
    simpa [route, rawRoute, terminal, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some routeSourcePoint := by
    simpa [route, rawRoute, routeSourcePoint] using
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have retained : RetainedRayPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
      retainedFinalOrdinaryFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex =
        retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    simpa [rawRoute, route, rawTerminal, terminal,
      finalPoint, slot] using
      retainedFinalOrdinaryFallbackOccurrenceRoute_eq_splicedOwnFigure7Route
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have fresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (retainedAngularFanSplicedOwnFigure7Route
            route terminal slot (route.getLastD (0, 0)))) := by
    have positionedFresh :=
      retainedFinalOrdinaryFallbackOccurrenceRoute_headNotInTail
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        choiceNone prefixLengthNe
    rw [routeEqual] at positionedFresh
    rw [routeLastD]
    exact positionedFresh
  have normalized :=
    retainedAngularFanSplicedOwnFigure7Route_normalized_firstDirection_of_headNotInTail
      route terminal slot routeSourcePoint routeLength classified
      routeHead routeOrthogonal retained fresh
  rw [routeEqual]
  rw [← routeLastD]
  exact normalized

end PeriodicOrthocrossing
end LeanTrominoes
