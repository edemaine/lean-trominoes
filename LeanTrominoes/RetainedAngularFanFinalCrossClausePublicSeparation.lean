import LeanTrominoes.RetainedAngularFanFinalDirectSourceCrossClauseOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackCompletePublicSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedPublicSeparation
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteSeparation

/-!
# Unconditional public cross-clause separation

The final copied-source route selector has four possible pairings: both
choices succeed, both fail, or exactly one succeeds.  The geometric work for
all four pairings is complete.  This file hides that implementation detail
behind the public total route family, leaving later global-planarity assembly
with only the structural distinction between equal and different clauses.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- Any two genuine copied-source routes belonging to different clauses in
the final coordinated family avoid each other, independently of which direct
route choices were available. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_avoidEachOther
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
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  cases firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
        formula firstClauseIndex firstLiteralIndex with
  | none =>
      cases secondChoiceLookup :
          retainedFinalDirectSourceRouteChoice?
            formula secondClauseIndex secondLiteralIndex with
      | none =>
          exact
            (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty
              firstClauseMember secondClauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup secondChoiceLookup
              clauseIndicesDifferent).toRoutesAvoidEachOther
      | some secondChoice =>
          exact
            (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_first_choice_none_second_some
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty secondChoice
              firstClauseMember secondClauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup secondChoiceLookup
              clauseIndicesDifferent).toRoutesAvoidEachOther
  | some firstChoice =>
      cases secondChoiceLookup :
          retainedFinalDirectSourceRouteChoice?
            formula secondClauseIndex secondLiteralIndex with
      | none =>
          exact
            (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_first_choice_some_second_none
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstChoice
              firstClauseMember secondClauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup secondChoiceLookup
              clauseIndicesDifferent).toRoutesAvoidEachOther
      | some secondChoice =>
          exact
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_avoidEachOther_of_choices_some
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstChoice secondChoice
              firstClauseMember secondClauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup secondChoiceLookup
              clauseIndicesDifferent

/-- Any two distinct copied-source incidence keys in the final coordinated
family avoid each other.  Indexed clause membership identifies the two clause
values when their indices agree, reducing that branch to the same-clause
theorem; unequal indices use the selector-free cross-clause theorem above. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_copiedSource_avoidEachOther
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
    (incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  by_cases clauseIndicesEqual :
      firstClauseIndex = secondClauseIndex
  · subst secondClauseIndex
    have firstClauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp firstClauseMember
    have secondClauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondClauseMember
    have clausesEqual : firstClause = secondClause := by
      have equality : some firstClause = some secondClause := by
        rw [← firstClauseLookup, ← secondClauseLookup]
      exact Option.some.inj equality
    subst secondClause
    have literalIndicesDifferent :
        firstLiteralIndex ≠ secondLiteralIndex := by
      exact incidencesDistinct.resolve_left (fun equal => equal rfl)
    exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        (by simpa [finalCoordinatedSource] using firstClauseMember)
        firstLiteralMember secondLiteralMember
        literalIndicesDifferent).1
  · exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_avoidEachOther
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesEqual

end PeriodicOrthocrossing
end LeanTrominoes
