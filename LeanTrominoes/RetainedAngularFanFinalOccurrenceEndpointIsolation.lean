import LeanTrominoes.RetainedAngularFanDirectOccurrenceEndpointIsolation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackEndpointIsolation

/-!
# Endpoint isolation for final copied-source occurrences

The final route selector has three genuine copied-source branches: a selected
direct atlas route, an ordinary fallback, and the singleton-prefix escaped
fallback.  Each branch now has the same unit-subdivided endpoint-isolation
certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Every genuine copied-source incidence in the final coordinated family
visits its variable endpoint only at the final subdivided point. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_source_lastNotInDropLast
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
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex)) := by
  have clauseLookup :
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
  cases choiceLookup :
      retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex with
  | none =>
      by_cases prefixLength :
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).dropLast.length = 1
      · rw [
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
            formula clauseIndex literalIndex
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal choiceLookup prefixLength clauseLookup literalLookup]
        exact
          retainedFinalEscapedFallbackOccurrenceRoute_lastNotInDropLast
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember choiceLookup
      · rw [
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
            formula clauseIndex literalIndex choiceLookup prefixLength]
        exact
          retainedFinalOrdinaryFallbackOccurrenceRoute_lastNotInDropLast
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember literalMember choiceLookup
  | some choice =>
      rw [
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
          formula clauseIndex literalIndex choice
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal choiceLookup clauseLookup literalLookup,
        retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice clauseMember literalMember choiceLookup]
      exact
        choice.completeFigure7Route_lastNotInDropLast
          (retainedFinalCoordinatedOccurrenceSlot
            formula literal clauseIndex literalIndex)

end PeriodicOrthocrossing
end LeanTrominoes
