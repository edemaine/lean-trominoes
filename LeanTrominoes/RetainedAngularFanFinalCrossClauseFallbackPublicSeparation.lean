import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackOccurrenceSeparation

/-!
# Public cross-clause fallback separation at distinct centers

The total final router chooses the escaped fallback exactly when deleting
the old variable endpoint leaves a singleton prefix.  The explicit
occurrence-route separator already covers ordinary/ordinary,
escaped/ordinary, and escaped/escaped joins at distinct variable centers.
This file performs the four prefix-length cases and transports those
certificates to the public coordinated route family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- Failed choices in different final source clauses and at distinct
canonical variable centers produce contact-free public coordinated routes,
including every combination of ordinary and singleton-prefix escaped
fallbacks. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_distinctCenters
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
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  have firstScaledClauseMember :
      (firstClause.scale retainedAngularFanSourceClearanceFactor,
          firstClauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(firstClause, firstClauseIndex), firstClauseMember, rfl⟩
  have secondScaledClauseMember :
      (secondClause.scale retainedAngularFanSourceClearanceFactor,
          secondClauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(secondClause, secondClauseIndex), secondClauseMember, rfl⟩
  have firstScaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp firstScaledClauseMember
  have secondScaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp secondScaledClauseMember
  have firstLiteralLookup :
      (firstClause.scale retainedAngularFanSourceClearanceFactor).literals[
          firstLiteralIndex]? =
        some firstLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp firstLiteralMember
  have secondLiteralLookup :
      (secondClause.scale retainedAngularFanSourceClearanceFactor).literals[
          secondLiteralIndex]? =
        some secondLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp secondLiteralMember
  have separated :=
    retainedFinalCrossClauseOrdinaryFallbackExplicitOccurrenceRoutes_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone clauseIndicesDifferent
  by_cases firstPrefixLength :
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast.length = 1
  · by_cases secondPrefixLength :
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex).dropLast.length = 1
    · rw [
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
          formula firstClauseIndex firstLiteralIndex
          (firstClause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral firstChoiceNone firstPrefixLength
          firstScaledClauseLookup firstLiteralLookup,
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
          formula secondClauseIndex secondLiteralIndex
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondChoiceNone secondPrefixLength
          secondScaledClauseLookup secondLiteralLookup]
      simpa only [retainedFinalEscapedFallbackOccurrenceRoute] using
        separated.2.2 centersDifferent
    · rw [
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
          formula firstClauseIndex firstLiteralIndex
          (firstClause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral firstChoiceNone firstPrefixLength
          firstScaledClauseLookup firstLiteralLookup,
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
          formula secondClauseIndex secondLiteralIndex
          secondChoiceNone secondPrefixLength,
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty secondClauseMember secondLiteralMember]
      simpa only [retainedFinalEscapedFallbackOccurrenceRoute] using
        separated.2.1 centersDifferent
  · by_cases secondPrefixLength :
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex).dropLast.length = 1
    · have separatedSwapped :=
        retainedFinalCrossClauseOrdinaryFallbackExplicitOccurrenceRoutes_strictlyAvoid
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondClauseMember firstClauseMember
          secondLiteralMember firstLiteralMember
          secondChoiceNone firstChoiceNone
          (Ne.symm clauseIndicesDifferent)
      rw [
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
          formula firstClauseIndex firstLiteralIndex
          firstChoiceNone firstPrefixLength,
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember firstLiteralMember,
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
          formula secondClauseIndex secondLiteralIndex
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondChoiceNone secondPrefixLength
          secondScaledClauseLookup secondLiteralLookup]
      simpa only [retainedFinalEscapedFallbackOccurrenceRoute] using
        (separatedSwapped.2.1 (Ne.symm centersDifferent)).symm
    · exact
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_prefix_lengths_ne_one
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          firstChoiceNone secondChoiceNone
          firstPrefixLength secondPrefixLength
          clauseIndicesDifferent

end PeriodicOrthocrossing
end LeanTrominoes
