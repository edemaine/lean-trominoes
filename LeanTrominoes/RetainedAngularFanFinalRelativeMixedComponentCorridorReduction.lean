import LeanTrominoes.RetainedFinalRouteCarrierBounds
import LeanTrominoes.RetainedAngularFanFinalDirectSourceTerminalClassification
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Relative mixed source corridors by physical component cases

A successful direct selector always comes from a direct noncarrier macrocell.
At an arbitrary relative shift, a failed selector is either another
macrocell or a carrier lens.  Two macrocell occurrences have distinct
physical centers, while separated carrier/macrocell rectangles are handled
by their enclosing bounds.  Thus only an overlapping carrier lens remains as
a local geometric callback.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Relative successful/failed source-corridor separation reduces to an
overlapping carrier-lens versus direct-macrocell occurrence. -/
theorem
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_componentCases
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
    (relativeTranslate : Cell)
    (carrierOverlap :
      ∀
        (fallbackCarrier :
          FinalGaugedCarrierRouteOccurrenceWitness
            formula fallbackClauseIndex fallbackLiteralIndex
              relativeTranslate)
        (directMacrocell :
          FinalGaugedRouteMacrocellOccurrenceWitness
            formula directClauseIndex directLiteralIndex (0, 0)),
        ¬ClosedGridRectanglesSeparated
            fallbackCarrier.rectangleLower
            fallbackCarrier.rectangleUpper
            (planarSATMacrocellRouteLower
              directMacrocell.translatedCenter)
            (planarSATMacrocellRouteUpper
              directMacrocell.translatedCenter) →
          SourcePrefixCorridorSeparated
            (translatePolyline
              ((finalCoordinatedPlacement formula).translation
                relativeTranslate)
              (finalCoordinatedSourceRoutes
                formula fallbackClauseIndex fallbackLiteralIndex))
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1) :
    SourcePrefixCorridorSeparated
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let placement := finalCoordinatedPlacement formula
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      (placement.translation relativeTranslate) fallbackRoute
  let directOccurrence :=
    finalGaugedRouteOccurrence
      formula directClauseIndex directLiteralIndex (0, 0)
  let fallbackOccurrence :=
    finalGaugedRouteOccurrence
      formula fallbackClauseIndex fallbackLiteralIndex relativeTranslate
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  have directOccurrenceEq : directOccurrence = directRoute := by
    exact
      (finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
        formula directClauseIndex directLiteralIndex).symm
  have fallbackOccurrenceEq :
      fallbackOccurrence = translatedFallbackRoute := by
    rfl
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
  have directComponentIsDirect :
      directWitness.metadata.source.component.IsDirect :=
    directWitness.componentIsDirect_of_finalChoiceSome
      formula choice choiceLookup
  have directNotCarrier :
      ¬∃ link,
        directWitness.metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at directComponentIsDirect
    simp [DrawingPlanarSATComponent.IsDirect] at directComponentIsDirect
  rcases
      directWitness.exists_macrocellOccurrenceWitness_of_not_carrier
        directNotCarrier with
    ⟨directMacrocell⟩
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
    simpa [translatedFallbackRoute, translatePolyline] using
      fallbackLength
  have directRetained : RetainedRayPolyline directRoute := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackRetained : RetainedRayPolyline fallbackRoute := by
    simpa [fallbackRoute] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackRetained :
      RetainedRayPolyline translatedFallbackRoute :=
    fallbackRetained.translate
      (placement.translation relativeTranslate)
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa [directRoute, directTerminal] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex
        choice choiceLookup
  have corridor_of_rectangles
      (rectangles :
        SourcePolylineRectanglesSeparated
          translatedFallbackRoute.dropLast directRoute) :
      SourcePrefixCorridorSeparated
        translatedFallbackRoute directRoute directTerminal.1 :=
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
      translatedFallbackRoute directRoute directTerminal
      translatedFallbackRetained directRetained
      translatedFallbackLength directLength directClassified
      rectangles
  rcases
      fallbackWitness.exists_carrier_or_macrocellOccurrenceWitness with
    fallbackCarrierCase | fallbackMacrocellCase
  · rcases fallbackCarrierCase with ⟨fallbackCarrier⟩
    by_cases rectanglesSeparated :
        ClosedGridRectanglesSeparated
          fallbackCarrier.rectangleLower
          fallbackCarrier.rectangleUpper
          (planarSATMacrocellRouteLower
            directMacrocell.translatedCenter)
          (planarSATMacrocellRouteUpper
            directMacrocell.translatedCenter)
    · apply corridor_of_rectangles
      have separated :=
        sourcePrefixPolylineRectanglesSeparated_of_carrierMacrocellOccurrences_of_rectanglesSeparated
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          fallbackCarrier directMacrocell rectanglesSeparated
      change
        SourcePolylineRectanglesSeparated
          fallbackOccurrence.dropLast directOccurrence at separated
      rw [fallbackOccurrenceEq, directOccurrenceEq] at separated
      exact separated
    · exact carrierOverlap
        fallbackCarrier directMacrocell rectanglesSeparated
  · rcases fallbackMacrocellCase with ⟨fallbackMacrocell⟩
    have centersDifferent :
        fallbackMacrocell.translatedCenter ≠
          directMacrocell.translatedCenter :=
      fallbackMacrocell.translatedCenter_ne_of_choice_none_of_second_choice_some
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        directMacrocell fallbackChoiceNone choice choiceLookup
    have rectangles :
        SourcePolylineRectanglesSeparated
          fallbackOccurrence.dropLast directOccurrence := by
      apply
        SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
          (firstLower :=
            planarSATMacrocellRouteLower
              fallbackMacrocell.translatedCenter)
          (firstUpper :=
            planarSATMacrocellRouteUpper
              fallbackMacrocell.translatedCenter)
          (secondLower :=
            planarSATMacrocellRouteLower
              directMacrocell.translatedCenter)
          (secondUpper :=
            planarSATMacrocellRouteUpper
              directMacrocell.translatedCenter)
      · intro point pointMember
        exact fallbackMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          fallbackMacrocell.center fallbackMacrocell.centerEq
          (List.mem_of_mem_dropLast pointMember)
      · intro point pointMember
        exact directMacrocell.routePoints_in_translatedMacrocell
          formula certificate.graphWellFormed
          certificate.graphDegreeAtMostThree certificate.graphIsLocal
          directMacrocell.center directMacrocell.centerEq pointMember
      · exact planarSATMacrocellRouteRectangles_separated
          centersDifferent
    apply corridor_of_rectangles
    change
      SourcePolylineRectanglesSeparated
        fallbackOccurrence.dropLast directOccurrence at rectangles
    rw [fallbackOccurrenceEq, directOccurrenceEq] at rectangles
    exact rectangles

end PeriodicOrthocrossing
end LeanTrominoes
