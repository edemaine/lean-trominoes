/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedCompleteSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedObliqueOccurrenceSeparation

/-!
# Reduction of copied-source relative separation to the two residual cases

The zero-shift branch is already the public within-cell separation theorem.
At a nonzero shift, successful/successful choices are separated by the
translated direct atlas, and an axis-aligned successful/failed pair is
separated by the completed mixed theorem.  Thus only a non-axis-aligned
successful/failed pair and a failed/failed pair remain geometric obligations.

This file records those two obligations and performs the complete selector
case split.  Keeping the reduction separate makes the remaining periodic
geometry explicit without duplicating the final drawing packaging.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The residual mixed-selector obligation: a non-axis-aligned successful
direct route strictly avoids a nontrivially translated failed-choice route. -/
def RetainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ (choice : RetainedDirectSourceRouteChoice)
    (directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (directClauseIndex fallbackClauseIndex : Nat),
      (directClause, directClauseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx →
      (fallbackClause, fallbackClauseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx →
      ∀ (directLiteral fallbackLiteral :
          PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
        (directLiteralIndex fallbackLiteralIndex : Nat),
        (directLiteral, directLiteralIndex) ∈
            directClause.literals.zipIdx →
        (fallbackLiteral, fallbackLiteralIndex) ∈
            fallbackClause.literals.zipIdx →
        retainedFinalDirectSourceRouteChoice?
            formula directClauseIndex directLiteralIndex = some choice →
        retainedFinalDirectSourceRouteChoice?
            formula fallbackClauseIndex fallbackLiteralIndex = none →
        ¬choice.sourceSegment.IsAxisAligned →
        ∀ relativeTranslate : Cell,
          relativeTranslate ≠ (0, 0) →
          RoutesStrictlyAvoidEachOther
            (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
              formula directClauseIndex directLiteralIndex)
            (translatePolyline
              ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula).translation relativeTranslate)
              (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
                formula fallbackClauseIndex fallbackLiteralIndex))

/-- The residual fallback-selector obligation: two failed-choice routes
strictly avoid one another at every nonzero relative shift. -/
def RetainedFinalFallbackRoutesRelativeStrictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ (firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (firstClauseIndex secondClauseIndex : Nat),
      (firstClause, firstClauseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx →
      (secondClause, secondClauseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx →
      ∀ (firstLiteral secondLiteral :
          PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
        (firstLiteralIndex secondLiteralIndex : Nat),
        (firstLiteral, firstLiteralIndex) ∈
            firstClause.literals.zipIdx →
        (secondLiteral, secondLiteralIndex) ∈
            secondClause.literals.zipIdx →
        retainedFinalDirectSourceRouteChoice?
            formula firstClauseIndex firstLiteralIndex = none →
        retainedFinalDirectSourceRouteChoice?
            formula secondClauseIndex secondLiteralIndex = none →
        ∀ relativeTranslate : Cell,
          relativeTranslate ≠ (0, 0) →
          RoutesStrictlyAvoidEachOther
            (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
              formula firstClauseIndex firstLiteralIndex)
            (translatePolyline
              ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula).translation relativeTranslate)
              (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
                formula secondClauseIndex secondLiteralIndex))

/-- The oblique successful/failed residual follows from the complete
occurrence theorem, including its internal split on physical target-center
equality. -/
theorem retainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    RetainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther formula := by
  intro choice directClause fallbackClause
    directClauseIndex fallbackClauseIndex
    directClauseMember fallbackClauseMember
    directLiteral fallbackLiteral
    directLiteralIndex fallbackLiteralIndex
    directLiteralMember fallbackLiteralMember
    choiceLookup fallbackChoiceNone directOblique
    relativeTranslate relativeTranslateNonzero
  exact
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_not_axisAligned_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero

/-- Reversing the relative shift turns the forward residual mixed theorem
into the failed/successful selector orientation. -/
theorem retainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther_reverse
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (obliqueMixed :
      RetainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther formula)
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
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
    obliqueMixed choice directClause fallbackClause
      directClauseIndex fallbackClauseIndex
      directClauseMember fallbackClauseMember
      directLiteral fallbackLiteral
      directLiteralIndex fallbackLiteralIndex
      directLiteralMember fallbackLiteralMember
      choiceLookup fallbackChoiceNone directOblique
      reverseTranslate reverseTranslateNonzero
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

/-- Once the two residual nonzero-shift obligations are supplied, every
pair of distinct copied-source route occurrences is relatively separated. -/
theorem retainedFinalCopiedSourceRoutes_relativeAvoidEachOther_of_residual
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (obliqueMixed :
      RetainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther formula)
    (fallbackFallback :
      RetainedFinalFallbackRoutesRelativeStrictlyAvoidEachOther formula) :
    RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula := by
  intro firstClause firstClauseIndex firstClauseMember
    firstLiteral firstLiteralIndex firstLiteralMember
    secondClause secondClauseIndex secondClauseMember
    secondLiteral secondLiteralIndex secondLiteralMember
    relativeTranslate occurrencesDifferent
  by_cases relativeTranslateZero : relativeTranslate = (0, 0)
  · subst relativeTranslate
    have incidencesDistinct :
        firstClauseIndex ≠ secondClauseIndex ∨
          firstLiteralIndex ≠ secondLiteralIndex := by
      by_contra notDistinct
      push Not at notDistinct
      apply occurrencesDifferent
      simp [notDistinct]
    have withinCell :=
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_copiedSource_avoidEachOther
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember incidencesDistinct
    have translationZero :
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation (0, 0) = (0, 0) := by
      simp [PeriodicVariablePlacement.translation, Cell.scale]
    simpa [translationZero] using withinCell
  · cases firstChoiceLookup :
        retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex with
    | none =>
        cases secondChoiceLookup :
            retainedFinalDirectSourceRouteChoice?
              formula secondClauseIndex secondLiteralIndex with
        | none =>
            exact
              (fallbackFallback firstClause secondClause
                firstClauseIndex secondClauseIndex
                firstClauseMember secondClauseMember
                firstLiteral secondLiteral
                firstLiteralIndex secondLiteralIndex
                firstLiteralMember secondLiteralMember
                firstChoiceLookup secondChoiceLookup
                relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther
        | some secondChoice =>
            by_cases secondAligned :
                secondChoice.sourceSegment.IsAxisAligned
            · exact
                (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_none_second_some_of_axisAligned_of_nonzero
                  formula sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty secondChoice
                  firstClauseMember secondClauseMember
                  firstLiteralMember secondLiteralMember
                  firstChoiceLookup secondChoiceLookup secondAligned
                  relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther
            · exact
                (retainedFinalObliqueMixedRoutesRelativeStrictlyAvoidEachOther_reverse
                  formula obliqueMixed secondChoice
                  firstClauseMember secondClauseMember
                  firstLiteralMember secondLiteralMember
                  firstChoiceLookup secondChoiceLookup secondAligned
                  relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther
    | some firstChoice =>
        cases secondChoiceLookup :
            retainedFinalDirectSourceRouteChoice?
              formula secondClauseIndex secondLiteralIndex with
        | none =>
            by_cases firstAligned :
                firstChoice.sourceSegment.IsAxisAligned
            · exact
                (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_axisAligned_of_nonzero
                  formula sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty firstChoice
                  firstClauseMember secondClauseMember
                  firstLiteralMember secondLiteralMember
                  firstChoiceLookup secondChoiceLookup firstAligned
                  relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther
            · exact
                (obliqueMixed firstChoice firstClause secondClause
                  firstClauseIndex secondClauseIndex
                  firstClauseMember secondClauseMember
                  firstLiteral secondLiteral
                  firstLiteralIndex secondLiteralIndex
                  firstLiteralMember secondLiteralMember
                  firstChoiceLookup secondChoiceLookup firstAligned
                  relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther
        | some secondChoice =>
            exact
              (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_direct_strictlyAvoid_translated_of_nonzero
                formula sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty firstChoice secondChoice
                firstClauseMember secondClauseMember
                firstLiteralMember secondLiteralMember
                firstChoiceLookup secondChoiceLookup
                relativeTranslate relativeTranslateZero).toRoutesAvoidEachOther

end PeriodicOrthocrossing
end LeanTrominoes
