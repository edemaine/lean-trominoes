/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeTranslatedFallbackOuterSeparation

/-!
# Translated fallback-boundary separation

The translated failed-choice boundary has the same two pieces as the stored
boundary: the fully refined retained source prefix and either the ordinary or
escaped outer replacement.  The translated source corridor separates the
first piece from an aligned direct route, while translated terminal rectangles
separate the second.  The generic splice assembly then handles both selector
branches uniformly.
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

/-- Avoiding the fully refined translated retained-source prefix and the
translated selected outer replacement suffices to avoid the actual translated
fallback boundary. -/
theorem
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
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
    (relativeTranslate : Cell)
    (other : List Cell)
    (prefixAvoid :
      let translatedRawRoute :=
        translatePolyline
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)
      RoutesStrictlyAvoidEachOther other
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline retainedAngularFanSourceClearanceFactor
            translatedRawRoute)).dropLast)
    (replacementAvoid :
      RoutesStrictlyAvoidEachOther other
        (retainedFinalTranslatedFallbackOuterReplacement
          formula literal clauseIndex literalIndex relativeTranslate)) :
    RoutesStrictlyAvoidEachOther other
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula literal clauseIndex literalIndex relativeTranslate) := by
  dsimp only at prefixAvoid
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
      rawRoute
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      translatedRawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have translatedRawLength : 2 ≤ translatedRawRoute.length := by
    simpa [translatedRawRoute, translatePolyline] using rawLength
  have routeLength : 2 ≤ route.length := by
    simpa [route, scalePolyline] using translatedRawLength
  have rawClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector rawRoute) = some rawTerminal := by
    simpa [rawRoute, rawTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have translatedRawClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector translatedRawRoute) = some rawTerminal := by
    simpa [translatedRawRoute, routeTerminalVector_translatePolyline] using
      rawClassified
  have routeClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) = some terminal := by
    simpa [route, terminal] using
      routeTerminalVector_scale_classified
        retainedAngularFanSourceClearanceFactor_pos
        translatedRawClassified
  have rawOrthogonal : OrthogonalPolyline rawRoute := by
    simpa [rawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have routeOrthogonal : OrthogonalPolyline route := by
    exact
      (rawOrthogonal.translate
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)).scalePolyline
        retainedAngularFanSourceClearanceFactor_pos
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [retainedFinalTranslatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix, if_pos]
    rw [← scalePolyline_translatePolyline']
    apply
      strictlyAvoids_retainedAngularFanEscapedSplicedBoundaryRoute_of_prefix_replacement
        other route terminal slot routeLength routeClassified
        routeOrthogonal escapeFits
    · simpa [route, translatedRawRoute, rawRoute] using prefixAvoid
    · unfold retainedFinalTranslatedFallbackOuterReplacement at replacementAvoid
      dsimp only at replacementAvoid
      rw [if_pos (by simpa [rawRoute] using singletonPrefix)] at replacementAvoid
      simpa [route, translatedRawRoute, rawRoute,
        terminal, rawTerminal, slot] using replacementAvoid
  · rw [retainedFinalTranslatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix]
    rw [← scalePolyline_translatePolyline']
    apply
      strictlyAvoids_retainedAngularFanSplicedBoundaryRoute_of_prefix_replacement
        other route terminal slot routeLength routeClassified routeOrthogonal
    · simpa [route, translatedRawRoute, rawRoute] using prefixAvoid
    · unfold retainedFinalTranslatedFallbackOuterReplacement at replacementAvoid
      dsimp only at replacementAvoid
      rw [if_neg (by simpa [rawRoute] using singletonPrefix)] at replacementAvoid
      simpa [route, translatedRawRoute, rawRoute,
        terminal, rawTerminal, slot] using replacementAvoid

/-- An aligned successful direct boundary strictly avoids the complete
translated failed-choice boundary at a nonzero shift with a distinct target. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_axisAligned
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
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex))
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
  have kindNe : choice.kind ≠ .routedClause := by
    intro kindEq
    exact
      (choice.sourceSegment_not_axisAligned_of_kind_eq_routedClause
        kindEq) directAligned
  have corridor :=
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_directSegment_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersDifferent
  apply
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate
      (choice.completeRoute directSlot)
  · have prefixAvoid :=
      retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
        formula translatedRawRoute
        directClauseIndex directLiteralIndex choice directSlot
        choiceLookup kindNe corridor
    dsimp only
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat]
    simpa only [directSlot, translatedRawRoute,
      retainedAngularFanSourceClearanceFactor,
      Nat.cast_ofNat] using prefixAvoid.symm
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directSlot
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersDifferent

end PeriodicOrthocrossing
end LeanTrominoes
