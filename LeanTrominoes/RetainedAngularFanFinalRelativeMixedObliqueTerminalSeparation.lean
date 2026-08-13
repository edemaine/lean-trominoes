/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCommonFrameTerminalSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedComponentCorridorReduction

/-!
# Relative oblique mixed terminal separation

The common-frame equality-lens calculation leaves only equality of the two
final endpoints.  For a direct route at shift zero and a translated failed
route, those endpoints are exactly their two physical canonical literal
centers.  Distinct centers therefore close the carrier-overlap branch.

The remaining component cases use their enclosing carrier or macrocell
rectangles.  This yields the final-segment rectangle certificate needed to
separate the two fully refined outer replacements.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- An oblique successful direct segment and a translated failed-choice
segment have separated endpoint rectangles whenever their physical canonical
literal centers differ. -/
theorem
    retainedFinalDirectTranslatedFallback_finalSegmentRectanglesSeparated_of_directSegment_not_axisAligned
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
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
    let translatedFallbackRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex)
    ClosedGridRectanglesSeparated
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (GridSegment.mk
        (polylineLastEntrance translatedFallbackRoute)
        (translatedFallbackRoute.getLastD (0, 0))).coordinateLower
      (GridSegment.mk
        (polylineLastEntrance translatedFallbackRoute)
        (translatedFallbackRoute.getLastD (0, 0))).coordinateUpper := by
  dsimp only
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      fallbackRoute
  have directOccurrenceEq :
      finalGaugedRouteOccurrence
          formula directClauseIndex directLiteralIndex (0, 0) =
        directRoute :=
    (finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
      formula directClauseIndex directLiteralIndex).symm
  have fallbackOccurrenceEq :
      finalGaugedRouteOccurrence
          formula fallbackClauseIndex fallbackLiteralIndex
            relativeTranslate =
        translatedFallbackRoute := by
    rfl
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackLength :
      2 ≤ translatedFallbackRoute.length := by
    simpa [translatedFallbackRoute, translatePolyline] using fallbackLength
  have directEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directLastD :
      directRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral := by
    rw [List.getLastD_eq_getLast?, directEndpoints.2]
    rfl
  have translatedFallbackLastD :
      translatedFallbackRoute.getLastD (0, 0) =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate) := by
    have fallbackNonempty : fallbackRoute ≠ [] := by
      intro fallbackNil
      rw [fallbackNil] at fallbackLength
      simp at fallbackLength
    change
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        fallbackRoute).getLastD (0, 0) = _
    rw [translatePolyline_getLastD _ fallbackRoute fallbackNonempty,
      List.getLastD_eq_getLast?, fallbackEndpoints.2]
    simp [Cell.add, add_comm]
  have representedSegment :
      (GridSegment.mk
        (polylineLastEntrance directRoute)
        (directRoute.getLastD (0, 0))) = choice.sourceSegment := by
    simpa [directRoute] using
      retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
        formula directClauseIndex directLiteralIndex choice choiceLookup
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        (directClause, directClauseIndex)
        (by simpa [finalCoordinatedSource] using directClauseMember)
        (directLiteral, directLiteralIndex) directLiteralMember
        (0, 0) with
    ⟨directWitness⟩
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        (fallbackClause, fallbackClauseIndex)
        (by simpa [finalCoordinatedSource] using fallbackClauseMember)
        (fallbackLiteral, fallbackLiteralIndex) fallbackLiteralMember
        relativeTranslate with
    ⟨fallbackWitness⟩
  have directComponent :
      directWitness.metadata.source.component.IsDirect :=
    directWitness.componentIsDirect_of_finalChoiceSome
      formula choice choiceLookup
  have directNotCarrier :
      ¬∃ link,
        directWitness.metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at directComponent
    simp [DrawingPlanarSATComponent.IsDirect] at directComponent
  rcases
      directWitness.exists_macrocellOccurrenceWitness_of_not_carrier
        directNotCarrier with
    ⟨directMacrocell⟩
  have directMacrocellComponent :
      directMacrocell.metadata.source.component.IsDirect :=
    directMacrocell.toFinalGaugedRouteOccurrenceWitness
      |>.componentIsDirect_of_finalChoiceSome
        formula choice choiceLookup
  let fallbackFinal : GridSegment :=
    GridSegment.mk
      (polylineLastEntrance translatedFallbackRoute)
      (translatedFallbackRoute.getLastD (0, 0))
  let directFinal : GridSegment :=
    GridSegment.mk
      (polylineLastEntrance directRoute)
      (directRoute.getLastD (0, 0))
  have fallbackFinalMember :
      fallbackFinal ∈ gridPolylineSegments translatedFallbackRoute :=
    finalGridSegment_mem translatedFallbackRoute translatedFallbackLength
  have directFinalMember :
      directFinal ∈ gridPolylineSegments directRoute :=
    finalGridSegment_mem directRoute directLength
  have fallbackFinalEndpoints :=
    gridPolylineSegments_endpoints_mem fallbackFinalMember
  have directFinalEndpoints :=
    gridPolylineSegments_endpoints_mem directFinalMember
  rcases
      fallbackWitness.exists_carrier_or_macrocellOccurrenceWitness with
    fallbackCarrierCase | fallbackMacrocellCase
  · rcases fallbackCarrierCase with ⟨fallbackCarrier⟩
    by_cases rectanglesSeparated :
        ClosedGridRectanglesSeparated
          fallbackCarrier.rectangleLower fallbackCarrier.rectangleUpper
          (planarSATMacrocellRouteLower directMacrocell.translatedCenter)
          (planarSATMacrocellRouteUpper directMacrocell.translatedCenter)
    · have separated :
          ClosedGridRectanglesSeparated
            fallbackFinal.coordinateLower fallbackFinal.coordinateUpper
            directFinal.coordinateLower directFinal.coordinateUpper := by
        apply
          GridSegment.coordinateRectanglesSeparated_of_inClosedGridRectangles
            (first := fallbackFinal) (second := directFinal)
        · exact fallbackCarrier.routePoints_in_rectangle
            formula certificate.graphWellFormed
            certificate.graphDegreeAtMostThree certificate.graphIsLocal
            (by simpa [fallbackOccurrenceEq] using fallbackFinalEndpoints.1)
        · exact fallbackCarrier.routePoints_in_rectangle
            formula certificate.graphWellFormed
            certificate.graphDegreeAtMostThree certificate.graphIsLocal
            (by simpa [fallbackOccurrenceEq] using fallbackFinalEndpoints.2)
        · exact directMacrocell.routePoints_in_translatedMacrocell
            formula certificate.graphWellFormed
            certificate.graphDegreeAtMostThree certificate.graphIsLocal
            directMacrocell.center directMacrocell.centerEq
            (by simpa [directOccurrenceEq] using directFinalEndpoints.1)
        · exact directMacrocell.routePoints_in_translatedMacrocell
            formula certificate.graphWellFormed
            certificate.graphDegreeAtMostThree certificate.graphIsLocal
            directMacrocell.center directMacrocell.centerEq
            (by simpa [directOccurrenceEq] using directFinalEndpoints.2)
        · exact rectanglesSeparated
      have separated' := separated.symm
      dsimp [directFinal] at separated'
      rw [representedSegment] at separated'
      simpa [fallbackFinal, translatedFallbackRoute, fallbackRoute] using
        separated'
    · have dichotomy :=
        fallbackCarrier.finalSegmentRectanglesSeparated_or_finish_eq_of_directChoice_of_notSeparated
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          directMacrocell choice choiceLookup
          directMacrocellComponent directOblique
          (by simpa [fallbackOccurrenceEq] using translatedFallbackLength)
          (by simpa [directOccurrenceEq] using directLength)
          rectanglesSeparated
      rcases dichotomy with separated | finishesEqual
      · rw [directOccurrenceEq, fallbackOccurrenceEq] at separated
        have separated' := separated.symm
        rw [representedSegment] at separated'
        simpa [fallbackFinal, translatedFallbackRoute, fallbackRoute] using
          separated'
      · exfalso
        apply centersDifferent
        have finishEq :
          translatedFallbackRoute.getLastD (0, 0) =
            directRoute.getLastD (0, 0) := by
          rw [← fallbackOccurrenceEq, ← directOccurrenceEq]
          simpa only using finishesEqual
        rw [translatedFallbackLastD, directLastD] at finishEq
        exact finishEq.symm
  · rcases fallbackMacrocellCase with ⟨fallbackMacrocell⟩
    have macrocellCentersDifferent :
        fallbackMacrocell.translatedCenter ≠
          directMacrocell.translatedCenter :=
      fallbackMacrocell.translatedCenter_ne_of_choice_none_of_second_choice_some
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        directMacrocell fallbackChoiceNone choice choiceLookup
    have separated :
        ClosedGridRectanglesSeparated
          fallbackFinal.coordinateLower fallbackFinal.coordinateUpper
          directFinal.coordinateLower directFinal.coordinateUpper := by
      apply
        GridSegment.coordinateRectanglesSeparated_of_inClosedGridRectangles
          (first := fallbackFinal) (second := directFinal)
      · exact fallbackMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          fallbackMacrocell.center fallbackMacrocell.centerEq
          (by simpa [fallbackOccurrenceEq] using fallbackFinalEndpoints.1)
      · exact fallbackMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          fallbackMacrocell.center fallbackMacrocell.centerEq
          (by simpa [fallbackOccurrenceEq] using fallbackFinalEndpoints.2)
      · exact directMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          directMacrocell.center directMacrocell.centerEq
          (by simpa [directOccurrenceEq] using directFinalEndpoints.1)
      · exact directMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          directMacrocell.center directMacrocell.centerEq
          (by simpa [directOccurrenceEq] using directFinalEndpoints.2)
      · exact planarSATMacrocellRouteRectangles_separated
          macrocellCentersDifferent
    have separated' := separated.symm
    dsimp [directFinal] at separated'
    rw [representedSegment] at separated'
    simpa [fallbackFinal, translatedFallbackRoute, fallbackRoute] using
      separated'

end PeriodicOrthocrossing
end LeanTrominoes
