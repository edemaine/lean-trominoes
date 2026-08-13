/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackEscapedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackPublicSeparation

/-!
# Complete public cross-clause fallback separation

The total router's singleton-prefix policy is now separated in all four
prefix-length cases at a shared variable center.  Combining that result with
the existing distinct-center theorem removes the final center inequality
from public cross-clause failed-choice separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- Failed choices in different final source clauses at the same canonical
variable center produce contact-free public coordinated routes. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_sameCenter
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
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
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
  by_cases firstPrefixLength :
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast.length = 1
  · have separated :=
      retainedFinalCrossClauseFallbackExplicitOccurrenceRouteCertificates_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone firstPrefixLength
        clauseIndicesDifferent centersEqual
    by_cases secondPrefixLength :
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
        separated.2 secondPrefixLength
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
        separated.1
  · by_cases secondPrefixLength :
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex).dropLast.length = 1
    · have separatedSwapped :=
        retainedFinalCrossClauseFallbackExplicitOccurrenceRouteCertificates_of_sameCenter
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondClauseMember firstClauseMember
          secondLiteralMember firstLiteralMember
          secondChoiceNone firstChoiceNone secondPrefixLength
          (Ne.symm clauseIndicesDifferent) centersEqual.symm
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
        separatedSwapped.1.symm
    · exact
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_prefix_lengths_ne_one
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          firstChoiceNone secondChoiceNone
          firstPrefixLength secondPrefixLength
          clauseIndicesDifferent

/-- Failed choices in different final source clauses produce contact-free
public coordinated routes, with no hypothesis on their variable centers. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none
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
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone
        clauseIndicesDifferent centersEqual
  · exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_distinctCenters
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone
        clauseIndicesDifferent centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
