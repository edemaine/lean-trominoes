/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOrdinaryFallbackRawHeadSeparation
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSourceHeadSeparation

/-! # Ordinary-fallback source-head separation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 500000

/-- For a genuine non-singleton failed-direct occurrence, the twice-scaled
source head is absent from both the unit-subdivided ordinary outer fan and
the unit-subdivided matching Figure 7 spoke. -/
theorem
    retainedFinalOrdinaryFallback_sourceHead_not_mem_outer_and_spoke
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
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (PeriodicThreeSATThree.routeTerminalVector rawRoute)
    let sourcePoint :=
      PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause
    let finalPoint :=
      PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor finalPoint)
    let terminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    let sourceHead :=
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor sourcePoint)
    sourceHead ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterCompleteRoute center terminal slot) ∧
      sourceHead ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanFigure7SpokeRouteAt center slot) := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (PeriodicThreeSATThree.routeTerminalVector rawRoute)
  let sourcePoint :=
    PositionedPeriodicCNF.canonicalClausePosition
      (finalCoordinatedPlacement formula) clause
  let finalPoint :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula) clause literal
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance rawRoute, rawRoute.getLastD (0, 0)⟩
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawFinal : rawRoute.getLast? = some finalPoint := by
    simpa [rawRoute, finalPoint] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  have rawLastD : rawRoute.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, rawFinal]
    rfl
  have separated :
      ClosedGridRectanglesSeparated
        sourcePoint sourcePoint
        finalSegment.coordinateLower finalSegment.coordinateUpper :=
    by
      simpa [rawRoute, sourcePoint, finalSegment] using
        finalCoordinatedFallbackSourceHead_finalSegmentRectanglesSeparated
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember
          choiceNone prefixLengthNe
  have clearance :
      288 <
        retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor := by
    rw [retainedTerminalFanTotalRefinement_eq,
      retainedAngularFanSourceClearanceFactor_eq]
    omega
  have rawClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector rawRoute) =
        some rawTerminal := by
    simpa [rawRoute, rawTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have absent :=
    retainedTerminalFanOuterAndSpoke_sourceHead_not_mem_of_separated
      retainedAngularFanSourceClearanceFactor_pos
      clearance rawRoute sourcePoint rawTerminal slot
      rawLength rawClassified separated
  dsimp only at absent
  have centerEq :
      Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            rawRoute).getLastD (0, 0)) =
        Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale retainedAngularFanSourceClearanceFactor
            finalPoint) := by
    rw [scalePolyline_getLastD, rawLastD]
  have sourceHeadEq :
      Cell.scale
          ((retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor : Nat) : Int)
          sourcePoint =
        Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale retainedAngularFanSourceClearanceFactor
            sourcePoint) := by
    rw [Cell.scale_scale, Nat.cast_mul]
  rw [centerEq, sourceHeadEq] at absent
  exact absent

end PeriodicOrthocrossing
end LeanTrominoes
