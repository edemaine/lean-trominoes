/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterFallbackSpokeSeparation

/-!
# Complete periodic same-center mixed occurrence separation

The direct and translated fallback occurrences each split into a boundary
prefix and a Figure 7 suffix.  The preceding same-center modules establish
all four cross interactions, so the standard two-by-two join theorem now
assembles strict separation of the complete occurrence routes.
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

/-- A successful aligned direct occurrence strictly avoids a complete
translated failed-choice occurrence at every nonzero shift whose physical
target center coincides with the direct target. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_sameCenter
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
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula fallbackClause fallbackLiteral
        fallbackClauseIndex fallbackLiteralIndex relativeTranslate) := by
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
  let directSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let fallbackBoundary :=
    retainedFinalTranslatedFallbackBoundaryPrefix
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
      relativeTranslate
  let fallbackSuffix :=
    translatePolyline physicalTranslate
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
  let fallbackBoundaryPoint :=
    Cell.add physicalTranslate
      (Cell.scale retainedTerminalFanRoutingRefinement
        (angularFanBoundaryPositionAt
          placement fallbackLiteral.atom
          (incidenceRelativeOffset
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
            fallbackLiteral)
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)))
  have fallbackSuffixHead :
      fallbackSuffix.head? = some fallbackBoundaryPoint := by
    simp [fallbackSuffix, fallbackBoundaryPoint,
      translatePolyline, scalePolyline,
      angularOccurrenceSuffix_head?]
  have fallbackBoundaryJoin :=
    retainedFinalTranslatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      relativeTranslate
  have fallbackBoundaryLast :
      fallbackBoundary.getLast? = some fallbackBoundaryPoint := by
    have joinEq :
        fallbackBoundary.getLast? = fallbackSuffix.head? := by
      simpa [source, placement, routes, fallbackBoundary,
        fallbackSuffix, physicalTranslate] using fallbackBoundaryJoin
    exact joinEq.trans fallbackSuffixHead
  have prefixBoundaryAvoid :=
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_axisAligned_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersEqual
  have spokePieceAvoid :=
    retainedFinalCoordinatedAlignedDirectOccurrencePieces_strictlyAvoid_translatedFallbackSuffix_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersEqual
  have directSuffixBoundaryAvoid :=
    retainedFinalCoordinatedAlignedDirectOccurrenceSuffix_strictlyAvoids_translatedFallbackBoundaryPrefix_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersEqual
  have assembled :=
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup fallbackBoundary fallbackSuffix fallbackBoundaryPoint
      fallbackBoundaryLast fallbackSuffixHead
      (by simpa [fallbackBoundary] using prefixBoundaryAvoid)
      (by simpa [source, placement, routes, fallbackSuffix,
        physicalTranslate] using spokePieceAvoid.1)
      (by simpa [source, placement, routes, directSuffix,
        fallbackBoundary] using directSuffixBoundaryAvoid)
      (by simpa [source, placement, routes, directSuffix,
        fallbackSuffix, physicalTranslate] using spokePieceAvoid.2)
  simpa [source, placement, routes, fallbackBoundary,
    fallbackSuffix, physicalTranslate,
    retainedFinalTranslatedFallbackOccurrenceRoute] using assembled

end PeriodicOrthocrossing
end LeanTrominoes
