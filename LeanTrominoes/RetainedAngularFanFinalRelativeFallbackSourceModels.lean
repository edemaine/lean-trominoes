/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceSpliceTranslation
import LeanTrominoes.RetainedAngularFanFinalRelativeDirectSourceModels
import LeanTrominoes.RetainedAngularFanFinalMixedPublicSeparation

/-!
# Translating final coordinated fallback-source routes

A translated failed-choice route retains the same singleton-prefix policy,
terminal classification, and occurrence slot.  Only its source splice and
Figure 7 suffix move by the physical drawing period.  The source splice can
equivalently be rebuilt from the retained route translated in the source
coordinate frame.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The selected fallback boundary rebuilt after translating its scaled
retained source route by one semantic period vector. -/
def retainedFinalTranslatedFallbackBoundaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell) : List Cell :=
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  let translatedRoute :=
    translatePolyline
      (Cell.scale retainedAngularFanSourceClearanceFactor sourceTranslate)
      route
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute))
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  if rawRoute.dropLast.length = 1 then
    retainedAngularFanEscapedSplicedBoundaryRoute
      translatedRoute terminal slot
  else
    retainedAngularFanSplicedBoundaryRoute
      translatedRoute terminal slot

/-- The complete translated fallback model, exposed as the translated
source boundary joined to the translated unchanged occurrence suffix. -/
def retainedFinalTranslatedFallbackOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell) : List Cell :=
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
  let suffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  joinAtEndpoint
    (retainedFinalTranslatedFallbackBoundaryPrefix
      formula literal clauseIndex literalIndex relativeTranslate)
    (translatePolyline physicalTranslate suffix)

/-- The physical drawing-period vector is the terminal refinement of the
source-scaled retained period vector. -/
theorem retainedFinalPhysicalTranslation_eq_refinedSourceTranslation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (relativeTranslate : Cell) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate =
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) := by
  rw [retainedFinalPhysicalTranslation_eq_directSourceFanPositioningOffset]
  simp [retainedDirectSourceFanPositioningOffset,
    retainedAngularFanSourceClearanceFactor]

/-- Translating the selected fallback boundary is exactly rebuilding it
from the translated retained source route. -/
theorem retainedFinalCoordinatedFallbackBoundaryPrefix_translate
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
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula literal clauseIndex literalIndex) =
      retainedFinalTranslatedFallbackBoundaryPrefix
        formula literal clauseIndex literalIndex relativeTranslate := by
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute))
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeNonempty : route ≠ [] := by
    intro routeEmpty
    have : route.length = 0 := by simp [routeEmpty]
    have routeLength : route.length = rawRoute.length := by
      simp [route, scalePolyline]
    omega
  rw [retainedFinalCoordinatedFallbackBoundaryPrefix,
    retainedFinalTranslatedFallbackBoundaryPrefix]
  rw [retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · have singletonPrefix' :
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).dropLast.length = 1 := by
      simpa [rawRoute] using singletonPrefix
    simp only [singletonPrefix', if_pos]
    simpa [route, terminal, slot, sourceTranslate] using
      retainedAngularFanEscapedSplicedBoundaryRoute_translate
        (Cell.scale retainedAngularFanSourceClearanceFactor sourceTranslate)
        route terminal slot routeNonempty
  · have singletonPrefix' :
        ¬(finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).dropLast.length = 1 := by
      simpa [rawRoute] using singletonPrefix
    simp only [singletonPrefix']
    simpa [route, terminal, slot, sourceTranslate] using
      retainedAngularFanSplicedBoundaryRoute_translate
        (Cell.scale retainedAngularFanSourceClearanceFactor sourceTranslate)
        route terminal slot routeNonempty

/-- The explicit policy-selected fallback route translates to the exposed
translated boundary/suffix model. -/
theorem retainedFinalFallbackOccurrenceRoute_translate
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
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedFinalFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex) =
      retainedFinalTranslatedFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex
        relativeTranslate := by
  rw [retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
    formula clause literal clauseIndex literalIndex]
  rw [translatePolyline_joinAtEndpoint,
    retainedFinalCoordinatedFallbackBoundaryPrefix_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember relativeTranslate]
  rfl

/-- At the public route interface, a failed selector has the same exact
translated fallback model. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_none
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
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) =
      retainedFinalTranslatedFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex
        relativeTranslate := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone]
  exact
    retainedFinalFallbackOccurrenceRoute_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember relativeTranslate

end PeriodicOrthocrossing
end LeanTrominoes
