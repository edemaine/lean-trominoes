import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterOccurrenceSeparation

/-!
# Complete aligned periodic mixed-selector separation

Distinct translated target centers use the global source-neighborhood
argument, while coincident physical target centers use strict local angular
order.  Splitting on that equality removes the last center hypothesis from
the aligned successful/failed route-family theorem; reversing the shift gives
the opposite selector orientation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every aligned successful direct route strictly avoids every nontrivially
translated failed-choice route, including shared physical target centers. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_axisAligned_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula directClauseIndex directLiteralIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex)) := by
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
  · rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember directLiteralMember
        choiceLookup,
      ← retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember directLiteralMember
        choiceLookup,
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_none
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
        fallbackChoiceNone relativeTranslate]
    exact
      retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersEqual
  · exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersEqual

/-- The reverse failed/successful selector orientation, obtained by applying
the complete forward theorem at the negative shift and translating back. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_none_second_some_of_axisAligned_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {fallbackClause directClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackClauseIndex directClauseIndex : Nat}
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {fallbackLiteral directLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackLiteralIndex directLiteralIndex : Nat}
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula directClauseIndex directLiteralIndex)) := by
  let reverseTranslate := Cell.neg relativeTranslate
  let physicalPlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula
  let backwardsPhysical :=
    physicalPlacement.translation reverseTranslate
  let forwardsPhysical :=
    physicalPlacement.translation relativeTranslate
  have reverseTranslateNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply relativeTranslateNonzero
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.neg, Cell.sub] at reverseZero ⊢
    omega
  have backwards :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_axisAligned_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned reverseTranslate
      reverseTranslateNonzero
  have shifted :=
    backwards.symm.translatePolyline forwardsPhysical
  have shiftCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, physicalPlacement,
      reverseTranslate, PeriodicVariablePlacement.translation,
      Cell.neg, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftCancel, translatePolyline_zero] at shifted
  simpa [backwardsPhysical, forwardsPhysical, physicalPlacement] using shifted

end PeriodicOrthocrossing
end LeanTrominoes
