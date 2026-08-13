/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterSpokeSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedFallbackSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedSpokeSeparation
import LeanTrominoes.RetainedAngularFanSourceSplicePointSeparation

/-!
# A selected fallback boundary avoids every other same-center spoke

This is the slot-parametric form of the fallback-boundary/suffix geometry.
It avoids requiring the other spoke to come from an untranslated stored
occurrence, which is essential when a nonzero periodic translate makes a
direct occurrence and a fallback occurrence share one physical fan center.
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

/-- Every positioned Figure 7 spoke lies in the radius-96 square around its
fan center. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_points_in_centerRectangle
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanFigure7SpokeRouteAt center slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 96 center)
      (coordinateRadiusUpper 96 center)
      point := by
  rw [← retainedTerminalFanCenteredFigure7Spoke_map_add] at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨offset, offsetMember, rfl⟩
  apply inClosedGridRectangle_coordinateRadius
  have bounded :=
    (retainedTerminalFanCenteredFigure7Spoke_points_within
      slot offset offsetMember).translate center
  simpa [Cell.add] using bounded

/-- The policy-selected fallback boundary avoids every other Figure 7 spoke
at its own fully refined fan center. -/
theorem
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_otherFigure7SpokeRouteAt
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
    (otherSlot : RetainedTerminalSlot)
    (slotsDifferent :
      retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex ≠ otherSlot) :
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal))
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula literal clauseIndex literalIndex)
      (retainedTerminalFanFigure7SpokeRouteAt center otherSlot) := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center otherSlot
  have routeLength : 2 ≤ route.length := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) = some terminal := by
    simpa [route, terminal, rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have rawOrthogonal : OrthogonalPolyline rawRoute := by
    simpa [rawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route] using
      rawOrthogonal.scalePolyline
        retainedAngularFanSourceClearanceFactor_pos
  have routeSimple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have terminalLengthPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal := by
    have escapePositive :
        0 < retainedTerminalFanOuterSourceEscapeLength := by
      native_decide
    omega
  have spokeBounded :
      ∀ point ∈ spoke,
        InClosedGridRectangle
          (coordinateRadiusLower 96 center)
          (coordinateRadiusUpper 96 center)
          point := by
    intro point pointMember
    exact
      retainedTerminalFanFigure7SpokeRouteAt_points_in_centerRectangle
        center otherSlot point (by simpa [spoke] using pointMember)
  have ordinaryReplacementAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          center terminal slot)
        spoke := by
    exact
      retainedTerminalFanOuterCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
        center terminal slot otherSlot terminalLengthPositive
        radialLengthPositive (by simpa [slot] using slotsDifferent)
  have ordinaryAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot)
        spoke := by
    simpa [center] using
      retainedAngularFanSplicedBoundaryPolyline_strictlyAvoids_ownPointNeighborhood_of_replacement
        route terminal slot finalPoint spoke routeLength classified
        routeSimple routeFinal
        (by simpa [center] using spokeBounded)
        (by simpa [center] using ordinaryReplacementAvoid)
  have ordinaryPolylineOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified routeOrthogonal
  have escapedPolylineOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot) :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified routeOrthogonal escapeFits
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · have scaledSingletonPrefix : route.dropLast.length = 1 := by
      simpa [route, rawRoute, scalePolyline] using singletonPrefix
    have routeLastD : route.getLastD (0, 0) = finalPoint := by
      rw [List.getLastD_eq_getLast?, routeFinal]
      rfl
    have escapedBoundaryEqual :
        retainedAngularFanEscapedSplicedBoundaryPolyline
            route terminal slot =
          retainedTerminalFanOuterEscapedCompleteRoute
            center terminal slot := by
      change
        retainedAngularFanEscapedSplicedBoundaryPolyline
            route terminal slot =
          retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
            terminal slot
      rw [← routeLastD]
      exact
        retainedAngularFanEscapedSplicedBoundaryPolyline_eq_outerCompleteRoute_of_singletonPrefix
          route terminal slot routeLength classified scaledSingletonPrefix
    have escapedAvoid :
        RoutesStrictlyAvoidEachOther
          (retainedAngularFanEscapedSplicedBoundaryPolyline
            route terminal slot)
          spoke := by
      rw [escapedBoundaryEqual]
      exact
        retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
          center terminal slot otherSlot terminalLengthPositive escapeFits
          (by simpa [slot] using slotsDifferent)
    rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix, if_pos]
    rw [retainedAngularFanEscapedSplicedBoundaryRoute,
      rasterizeRetainedPolyline_eq_of_orthogonal
        escapedPolylineOrthogonal]
    simpa [rawRoute, rawTerminal, route, terminal, slot,
      finalPoint, center, spoke] using
      escapedAvoid
  · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix]
    rw [retainedAngularFanSplicedBoundaryRoute,
      rasterizeRetainedPolyline_eq_of_orthogonal
        ordinaryPolylineOrthogonal]
    simpa [rawRoute, rawTerminal, route, terminal, slot,
      finalPoint, center, spoke] using
      ordinaryAvoid

/-- Translating any fallback-centered spoke to a shared physical target
produces the corresponding positioned direct-choice spoke. -/
theorem
    retainedFinalTranslatedFallbackFigure7SpokeRouteAt_eq_directFigure7Spoke_of_sameCenter
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
    {directClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate))
    (slot : RetainedTerminalSlot) :
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    let fallbackCenter :=
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral))
    translatePolyline physicalTranslate
        (retainedTerminalFanFigure7SpokeRouteAt fallbackCenter slot) =
      choice.figure7Spoke slot := by
  dsimp only
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral))
  have centerEq :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.add physicalTranslate fallbackCenter := by
    simpa [physicalTranslate, fallbackCenter] using
      retainedFinalDirectPositionedFanCenter_eq_add_translatedFallbackCanonicalFanCenter_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember
        directLiteralMember choiceLookup relativeTranslate centersEqual
  calc
    translatePolyline physicalTranslate
        (retainedTerminalFanFigure7SpokeRouteAt fallbackCenter slot) =
      retainedTerminalFanFigure7SpokeRouteAt
        (Cell.add physicalTranslate fallbackCenter) slot :=
      translatePolyline_retainedTerminalFanFigure7SpokeRouteAt
        physicalTranslate fallbackCenter slot
    _ = retainedTerminalFanFigure7SpokeRouteAt
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) slot := by
      rw [centerEq]
    _ = choice.figure7Spoke slot :=
      (retainedDirectSourceRouteChoice_figure7Spoke_eq_spokeRouteAt
        choice slot).symm

/-- At a nonzero shared-center shift, the direct Figure 7 suffix strictly
avoids the translated selected fallback boundary. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrenceSuffix_strictlyAvoids_translatedFallbackBoundaryPrefix_of_sameCenter
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
    RoutesStrictlyAvoidEachOther directSuffix
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  dsimp only
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral))
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have angularOrder :=
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersEqual
  have slotsDifferent : fallbackSlot ≠ directSlot := by
    exact
      (directFallbackStrictAngularOrderCompatible_slots_ne
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        (classifiedRetainedTerminalData
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula fallbackClauseIndex fallbackLiteralIndex))).1
        directSlot fallbackSlot
        (by simpa [directSlot, fallbackSlot] using angularOrder)).symm
  have localAvoid :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_otherFigure7SpokeRouteAt
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone directSlot
      (by simpa [fallbackSlot] using slotsDifferent)
  have translatedAvoid :=
    localAvoid.translatePolyline physicalTranslate
  have translatedSpokeEq :
      translatePolyline physicalTranslate
          (retainedTerminalFanFigure7SpokeRouteAt
            fallbackCenter directSlot) =
        choice.figure7Spoke directSlot := by
    simpa [physicalTranslate, fallbackCenter] using
      retainedFinalTranslatedFallbackFigure7SpokeRouteAt_eq_directFigure7Spoke_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember
        directLiteralMember choiceLookup relativeTranslate centersEqual
        directSlot
  have directSuffixEq :=
    retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup
  dsimp only at directSuffixEq
  rw [retainedFinalCoordinatedFallbackBoundaryPrefix_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      relativeTranslate,
    translatedSpokeEq, directSuffixEq] at translatedAvoid
  simpa [fallbackCenter, physicalTranslate,
    finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes] using translatedAvoid.symm

end PeriodicOrthocrossing
end LeanTrominoes
