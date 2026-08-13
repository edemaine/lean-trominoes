/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackDistinctCenterBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSameCenterOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedOccurrenceSeparation

/-!
# Distinct-center translated fallback occurrence separation

The distinct-center boundary theorem handles the two source-side pieces.
The existing point-neighborhood theorem separates either unchanged Figure 7
suffix from the complete fallback occurrence at the other target.  Applying
it in both relative orientations and translating one certificate back gives
the remaining interactions, after which the two endpoint joins assemble the
complete occurrence routes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Reversing a relative shift reverses the distinct-center relation. -/
private theorem reverseFallbackCanonicalCentersDifferent
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement secondClause secondLiteral)
          (placement.translation relativeTranslate)) :
    PositionedPeriodicCNF.canonicalLiteralPosition
        placement secondClause secondLiteral ≠
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral)
        (placement.translation (Cell.neg relativeTranslate)) := by
  intro reverseEqual
  apply centersDifferent
  rcases firstCenterEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
        placement firstClause firstLiteral with
    ⟨firstX, firstY⟩
  rcases secondCenterEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
        placement secondClause secondLiteral with
    ⟨secondX, secondY⟩
  rcases relativeTranslate with ⟨translateX, translateY⟩
  simp [firstCenterEq, secondCenterEq,
    PeriodicVariablePlacement.translation,
    Cell.neg, Cell.sub, Cell.add, Cell.scale] at reverseEqual ⊢
  omega

/-- At distinct translated targets, the first complete failed-choice
occurrence route is strictly separated from the translated second one. -/
theorem
    retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_distinctCenter
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
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalFallbackOccurrenceRoute
        formula firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate) := by
  let firstBoundary :=
    retainedFinalCoordinatedFallbackBoundaryPrefix
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let translatedSecondBoundary :=
    retainedFinalTranslatedFallbackBoundaryPrefix
      formula secondLiteral secondClauseIndex secondLiteralIndex
      relativeTranslate
  let firstSuffix :=
    retainedFinalFallbackOccurrenceSuffix
      formula firstClause firstLiteral
      firstClauseIndex firstLiteralIndex
  let translatedSecondSuffix :=
    retainedFinalTranslatedFallbackOccurrenceSuffix
      formula secondClause secondLiteral
      secondClauseIndex secondLiteralIndex relativeTranslate
  have boundariesAvoid :
      RoutesStrictlyAvoidEachOther firstBoundary translatedSecondBoundary := by
    simpa [firstBoundary, translatedSecondBoundary] using
      retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_translated_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersDifferent
  have firstSuffixAvoidSecondOccurrence :
      RoutesStrictlyAvoidEachOther firstSuffix
        (retainedFinalTranslatedFallbackOccurrenceRoute
          formula secondClause secondLiteral
          secondClauseIndex secondLiteralIndex relativeTranslate) := by
    simpa [firstSuffix, retainedFinalFallbackOccurrenceSuffix] using
      (retainedFinalTranslatedFallbackOccurrenceRoute_strictlyAvoids_directOccurrenceSuffix_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember secondChoiceNone
        relativeTranslate centersDifferent).symm
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let firstBoundaryPoint :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset
          (firstClause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          firstLiteral firstClauseIndex firstLiteralIndex))
  let secondBoundaryPoint :=
    Cell.add
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (angularFanBoundaryPositionAt
          placement secondLiteral.atom
          (incidenceRelativeOffset
            (secondClause.scale retainedAngularFanSourceClearanceFactor)
            secondLiteral)
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            secondLiteral secondClauseIndex secondLiteralIndex)))
  have firstSuffixHead : firstSuffix.head? = some firstBoundaryPoint := by
    simp [firstSuffix, retainedFinalFallbackOccurrenceSuffix,
      firstBoundaryPoint, source, placement, routes,
      angularOccurrenceSuffix_head?]
  have secondSuffixHead :
      translatedSecondSuffix.head? = some secondBoundaryPoint := by
    simp [translatedSecondSuffix,
      retainedFinalTranslatedFallbackOccurrenceSuffix,
      retainedFinalFallbackOccurrenceSuffix,
      secondBoundaryPoint, source, placement, routes,
      translatePolyline, angularOccurrenceSuffix_head?]
  have firstBoundaryJoin :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have firstBoundaryLast :
      firstBoundary.getLast? = some firstBoundaryPoint := by
    have joinEq : firstBoundary.getLast? = firstSuffix.head? := by
      simpa [firstBoundary, firstSuffix,
        retainedFinalFallbackOccurrenceSuffix,
        source, placement, routes] using firstBoundaryJoin
    exact joinEq.trans firstSuffixHead
  have secondBoundaryJoin :=
    retainedFinalTranslatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      relativeTranslate
  have secondBoundaryLast :
      translatedSecondBoundary.getLast? = some secondBoundaryPoint := by
    have joinEq :
        translatedSecondBoundary.getLast? =
          translatedSecondSuffix.head? := by
      simpa [translatedSecondBoundary, translatedSecondSuffix,
        retainedFinalTranslatedFallbackOccurrenceSuffix,
        retainedFinalFallbackOccurrenceSuffix,
        source, placement, routes] using secondBoundaryJoin
    exact joinEq.trans secondSuffixHead
  have firstSuffixAvoidPieces :
      RoutesStrictlyAvoidEachOther firstSuffix translatedSecondBoundary ∧
        RoutesStrictlyAvoidEachOther firstSuffix translatedSecondSuffix := by
    apply firstSuffixAvoidSecondOccurrence.of_join_right
      secondBoundaryLast secondSuffixHead
  have firstOccurrenceAvoidSecondSuffix :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint firstBoundary firstSuffix)
        translatedSecondSuffix := by
    let reverseTranslate := Cell.neg relativeTranslate
    let physicalPlacement :=
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula
    let backwardsPhysical := physicalPlacement.translation reverseTranslate
    let forwardsPhysical := physicalPlacement.translation relativeTranslate
    have reverseCentersDifferent :
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral ≠
          Cell.add
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (finalCoordinatedPlacement formula) firstClause firstLiteral)
            ((finalCoordinatedPlacement formula).translation
              reverseTranslate) := by
      simpa [reverseTranslate] using
        reverseFallbackCanonicalCentersDifferent
          (finalCoordinatedPlacement formula)
          firstClause secondClause firstLiteral secondLiteral
          relativeTranslate centersDifferent
    have backwards :=
      retainedFinalTranslatedFallbackOccurrenceRoute_strictlyAvoids_directOccurrenceSuffix_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember firstClauseMember
        secondLiteralMember firstLiteralMember firstChoiceNone
        reverseTranslate reverseCentersDifferent
    rw [← retainedFinalFallbackOccurrenceRoute_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      reverseTranslate] at backwards
    have shifted := backwards.translatePolyline forwardsPhysical
    have shiftCancel :
        Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
      rcases relativeTranslate with ⟨translateX, translateY⟩
      simp [backwardsPhysical, forwardsPhysical, physicalPlacement,
        reverseTranslate, PeriodicVariablePlacement.translation,
        Cell.neg, Cell.sub, Cell.add, Cell.scale]
    rw [translatePolyline_add, shiftCancel, translatePolyline_zero] at shifted
    rw [retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
      formula firstClause firstLiteral firstClauseIndex firstLiteralIndex]
      at shifted
    simpa [firstBoundary, firstSuffix, translatedSecondSuffix,
      retainedFinalTranslatedFallbackOccurrenceSuffix,
      retainedFinalFallbackOccurrenceSuffix, backwardsPhysical,
      forwardsPhysical, physicalPlacement] using shifted
  have firstOccurrenceAvoidSecondBoundary :=
    boundariesAvoid.join_left firstSuffixAvoidPieces.1
      firstBoundaryLast firstSuffixHead
  have assembled :=
    firstOccurrenceAvoidSecondBoundary.join_right
      firstOccurrenceAvoidSecondSuffix
      secondBoundaryLast secondSuffixHead
  rw [retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
    formula firstClause firstLiteral firstClauseIndex firstLiteralIndex]
  change RoutesStrictlyAvoidEachOther
    (joinAtEndpoint firstBoundary firstSuffix)
    (joinAtEndpoint translatedSecondBoundary translatedSecondSuffix)
  exact assembled

end PeriodicOrthocrossing
end LeanTrominoes
