import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackDistinctCenterOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeCopiedSourceReduction

/-!
# Complete translated fallback-route separation

The same-center and distinct-center occurrence theorems cover the exhaustive
comparison of canonical variable targets.  This file combines those branches
and discharges the failed/failed residual obligation at the public retained
route interface.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Complete failed-choice occurrence routes strictly avoid one another at
every nonzero relative shift. -/
theorem retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
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
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalFallbackOccurrenceRoute
        formula firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate) := by
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
  · exact
      retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersEqual
  · exact
      retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersEqual

/-- The failed/failed residual proposition used by copied-source relative
separation is fully discharged. -/
theorem retainedFinalFallbackRoutes_relativeStrictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ []) :
    RetainedFinalFallbackRoutesRelativeStrictlyAvoidEachOther formula := by
  intro firstClause secondClause firstClauseIndex secondClauseIndex
    firstClauseMember secondClauseMember
    firstLiteral secondLiteral firstLiteralIndex secondLiteralIndex
    firstLiteralMember secondLiteralMember firstChoiceNone secondChoiceNone
    relativeTranslate relativeTranslateNonzero
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstChoiceNone,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      secondChoiceNone relativeTranslate]
  exact
    retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember firstChoiceNone secondChoiceNone
      relativeTranslate relativeTranslateNonzero

/-- All copied-source route occurrences are relatively separated.  The
selector reduction is now closed by the complete oblique mixed and
failed/failed theorems. -/
theorem retainedFinalCopiedSourceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ []) :
    RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula :=
  retainedFinalCopiedSourceRoutes_relativeAvoidEachOther_of_residual
    formula sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
    (retainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther
      formula sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
    (retainedFinalFallbackRoutes_relativeStrictlyAvoidEachOther
      formula sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)

/-- The final normalized fixed-eight periodic incidence drawing satisfies the
complete ribbon-ready interface required by the tiling construction. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_isRibbonReady
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ []) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).IsRibbonReady :=
  retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_isRibbonReady_of_copiedSourceRelative
    formula sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
    (retainedFinalCopiedSourceRoutes_relativeAvoidEachOther
      formula sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
