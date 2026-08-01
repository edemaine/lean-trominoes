import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation

/-!
# Coordinated fallback occurrences avoid their matching cycle

The public final route family selects between the ordinary and delayed-lane
fallbacks according to the copied source prefix length.  This module exposes
the two branch certificates behind that exact total-family case split.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 10000

/-- Every failed-choice occurrence in the public final coordinated route
family avoids its matching periodically lifted implication cycle, whether
the selector chooses the ordinary or delayed-lane fallback. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_matchingCycleLift
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
    (cycleClauseIndex cycleLiteralIndex : Nat)
    (cycleClauseIndexLt :
      cycleClauseIndex < presentedCycleVertices.length)
    (cycleLiteralIndexLt : cycleLiteralIndex < 2) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (retainedFinalMatchingCycleLift
        formula clause literal
        cycleClauseIndex cycleLiteralIndex) := by
  by_cases prefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1
  · have clauseLookup :
        finalCoordinatedScaledClause? formula clauseIndex =
          some
            (clause.scale retainedAngularFanSourceClearanceFactor) := by
      have rawClauseLookup :
          (finalCoordinatedSource formula).clauses[clauseIndex]? =
            some clause :=
        (List.mem_zipIdx_iff_getElem?
          (x := (clause, clauseIndex))
          (l := (finalCoordinatedSource formula).clauses)).mp
            clauseMember
      unfold finalCoordinatedScaledClause?
      rw [PositionedPeriodicCNF.scale_clauses,
        List.getElem?_map, rawClauseLookup]
      rfl
    have literalLookup :
        (clause.scale
          retainedAngularFanSourceClearanceFactor).literals[literalIndex]? =
            some literal := by
      simpa only [PositionedPeriodicClause.scale_literals] using
        (List.mem_zipIdx_iff_getElem?
          (x := (literal, literalIndex))
          (l := clause.literals)).mp literalMember
    have routeEqual :=
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
        formula clauseIndex literalIndex
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal choiceNone prefixLength clauseLookup literalLookup
    have avoids :=
      retainedFinalEscapedFallbackOccurrenceRoute_avoids_matchingCycleLift
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        cycleClauseIndex cycleLiteralIndex
        cycleClauseIndexLt cycleLiteralIndexLt
    rw [routeEqual]
    exact avoids
  · have routeEqual :=
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
        formula clauseIndex literalIndex choiceNone prefixLength
    have avoids :=
      retainedFinalOrdinaryFallbackOccurrenceRoute_avoids_matchingCycleLift
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        cycleClauseIndex cycleLiteralIndex
        cycleClauseIndexLt cycleLiteralIndexLt
    rw [routeEqual]
    exact avoids

end PeriodicOrthocrossing
end LeanTrominoes
