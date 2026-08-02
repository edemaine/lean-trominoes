import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Classification of final fallback source segments

The retained classifier is phrased using a route's terminal-vector helper.
Mixed direct/fallback geometry instead compares the explicit final segment.
This module transfers the classification to those two segment endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The classifier of a genuine final source route also classifies its
explicit penultimate-to-final segment. -/
theorem finalCoordinatedSourceRoute_finalSegment_classified
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
    retainedTerminalDirectionClassify
        (Cell.sub
          (polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex))
          ((finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).getLastD (0, 0))) =
      some
        (classifiedRetainedTerminalData
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex))) := by
  rw [← routeTerminalVector_eq_sub_lastEntrance]
  · exact finalCoordinatedSourceRoute_classified
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  · exact finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
