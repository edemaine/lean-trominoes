/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSameCenterData
import LeanTrominoes.RetainedAngularFanSourceMixedSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSplicePointSeparation

/-!
# Relative fallback source-prefix/outer-fan separation

At a nonzero period shift, the translated prefix of one failed-choice
source route is strictly separated from the selected outer replacement of
another.  The proof is independent of whether their final variable centers
coincide.  It is factored into corridor, point-clearance, and final-segment
interfaces so the ordinary and delayed-lane policies remain separate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The translated failed-choice source prefix clears the final point of
another failed-choice source route, both as listed points and along its
axis-aligned segments. -/
theorem
    retainedFinalTranslatedFallbackSourcePrefix_avoids_fallbackCenter_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {referenceClause translatedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceClauseIndex translatedClauseIndex : Nat}
    (referenceClauseMember :
      (referenceClause, referenceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (translatedClauseMember :
      (translatedClause, translatedClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {referenceLiteral translatedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceLiteralIndex translatedLiteralIndex : Nat}
    (referenceLiteralMember :
      (referenceLiteral, referenceLiteralIndex) ∈
        referenceClause.literals.zipIdx)
    (translatedLiteralMember :
      (translatedLiteral, translatedLiteralIndex) ∈
        translatedClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula translatedClauseIndex translatedLiteralIndex)
    let referenceCenter :=
      PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        referenceClause referenceLiteral
    (∀ point ∈ translatedRoute.dropLast, point ≠ referenceCenter) ∧
      ∀ segment ∈ gridPolylineSegments translatedRoute.dropLast,
        segment.IsAxisAligned → ¬segment.Contains referenceCenter := by
  dsimp only
  let referenceRoute :=
    finalCoordinatedSourceRoutes
      formula referenceClauseIndex referenceLiteralIndex
  let translatedRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula translatedClauseIndex translatedLiteralIndex)
  let referenceCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      referenceClause referenceLiteral
  have prefixAvoidRoute :
      RoutesStrictlyAvoidEachOther
        translatedRoute.dropLast referenceRoute := by
    simpa [referenceRoute, translatedRoute] using
      finalCoordinatedTranslatedSecondSourceRoutePrefix_strictlyAvoids_firstSourceRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember translatedClauseMember
        referenceLiteralMember translatedLiteralMember
        relativeTranslate relativeTranslateNonzero
  have referenceLast : referenceRoute.getLast? = some referenceCenter := by
    simpa [referenceRoute, referenceCenter] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember).2
  have referenceCenterMember : referenceCenter ∈ referenceRoute :=
    mem_of_getLast?_eq_some referenceLast
  have pointAvoid :
      ∀ point ∈ translatedRoute.dropLast, point ≠ referenceCenter := by
    intro point pointMember pointsEqual
    exact
      prefixAvoidRoute.2.2.2 point pointMember
        referenceCenter referenceCenterMember pointsEqual
  refine ⟨pointAvoid, ?_⟩
  intro segment segmentMember _segmentAligned contains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        contains with interior | endpoint
  · exact
      prefixAvoidRoute.2.2.1 referenceCenter referenceCenterMember
        segment segmentMember interior
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    rcases endpoint with atStart | atFinish
    · exact (pointAvoid segment.start endpoints.1) atStart.symm
    · exact (pointAvoid segment.finish endpoints.2) atFinish.symm

/-- The translated failed-choice prefix strictly avoids the discarded final
segment of another source route. -/
theorem
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackFinalSegment_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {referenceClause translatedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceClauseIndex translatedClauseIndex : Nat}
    (referenceClauseMember :
      (referenceClause, referenceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (translatedClauseMember :
      (translatedClause, translatedClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {referenceLiteral translatedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceLiteralIndex translatedLiteralIndex : Nat}
    (referenceLiteralMember :
      (referenceLiteral, referenceLiteralIndex) ∈
        referenceClause.literals.zipIdx)
    (translatedLiteralMember :
      (translatedLiteral, translatedLiteralIndex) ∈
        translatedClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let referenceRoute :=
      finalCoordinatedSourceRoutes
        formula referenceClauseIndex referenceLiteralIndex
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula translatedClauseIndex translatedLiteralIndex)
    RoutesStrictlyAvoidEachOther translatedRoute.dropLast
      [polylineLastEntrance referenceRoute,
        referenceRoute.getLastD (0, 0)] := by
  dsimp only
  let referenceRoute :=
    finalCoordinatedSourceRoutes
      formula referenceClauseIndex referenceLiteralIndex
  let translatedRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula translatedClauseIndex translatedLiteralIndex)
  have referenceLength : 2 ≤ referenceRoute.length := by
    simpa [referenceRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have rawAvoid : RoutesAvoidEachOther translatedRoute referenceRoute := by
    simpa [referenceRoute, translatedRoute] using
      routesAvoidEachOther_comm
        (finalCoordinatedSourceRoutes_avoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember translatedClauseMember
        referenceLiteralMember translatedLiteralMember
        relativeTranslate relativeTranslateNonzero)
  have prefixesAvoid :
      RoutesStrictlyAvoidEachOther
        translatedRoute.dropLast referenceRoute.dropLast := by
    simpa [referenceRoute, translatedRoute] using
      (finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember translatedClauseMember
        referenceLiteralMember translatedLiteralMember
        relativeTranslate relativeTranslateNonzero).symm
  have referenceEntrance :
      referenceRoute.dropLast.getLast? =
        some (polylineLastEntrance referenceRoute) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec
        (exists_reverse_tail_head?_of_two_le_length
          referenceRoute referenceLength))
  let referenceCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      referenceClause referenceLiteral
  have referenceLast : referenceRoute.getLast? = some referenceCenter := by
    simpa [referenceRoute, referenceCenter] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember).2
  have referenceLastD : referenceRoute.getLastD (0, 0) = referenceCenter := by
    simp [List.getLastD_eq_getLast?, referenceLast]
  have pointClearance :=
    (retainedFinalTranslatedFallbackSourcePrefix_avoids_fallbackCenter_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty referenceClauseMember translatedClauseMember
      referenceLiteralMember translatedLiteralMember
      relativeTranslate relativeTranslateNonzero).1
  rw [referenceLastD]
  exact
    routesStrictlyAvoidEachOther_dropLast_finalSegment
      rawAvoid prefixesAvoid referenceEntrance referenceLast
      (by simpa [translatedRoute, referenceCenter] using pointClearance)

/-- A source-first refined prefix avoids an ordinary complete outer fan
around an axis-aligned discarded terminal segment. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerCompleteRoute_of_axisAligned
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector referenceRoute) = some referenceTerminal)
    (referenceAligned :
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (sourceAvoids :
      RoutesStrictlyAvoidEachOther sourceRoute.dropLast
        [polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)]) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor referenceRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  let combinedFactor := retainedTerminalFanTotalRefinement * factor
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  have combinedPositive : 0 < combinedFactor := by
    exact Nat.mul_pos (by native_decide) (by omega)
  have radiusLt : 288 < combinedFactor := by
    dsimp [combinedFactor]
    rw [retainedTerminalFanTotalRefinement_eq]
    omega
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_axisAlignedSegmentNeighborhood
      (source := sourceRoute.dropLast)
      (nearby :=
        retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor referenceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor referenceTerminal)
          referenceSlot)
      (reference := referenceSegment)
      combinedPositive radiusLt
      (by simpa [referenceSegment] using referenceAligned)
      (by simpa [referenceSegment] using sourceAvoids)
      (by
        intro point pointMember
        simpa [combinedFactor, referenceSegment] using
          retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
            referenceRoute referenceTerminal referenceSlot
            referenceLength referenceClassified pointMember)
  simpa [combinedFactor, scalePolyline_scalePolyline_nat,
    scalePolyline, List.map_map, Function.comp_def,
    Cell.scale_scale, Nat.cast_mul] using separated

/-- The fully refined translated fallback prefix avoids the ordinary outer
replacement of another fallback. -/
theorem
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_ordinaryFallbackOuter_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {referenceClause translatedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceClauseIndex translatedClauseIndex : Nat}
    (referenceClauseMember :
      (referenceClause, referenceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (translatedClauseMember :
      (translatedClause, translatedClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {referenceLiteral translatedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceLiteralIndex translatedLiteralIndex : Nat}
    (referenceLiteralMember :
      (referenceLiteral, referenceLiteralIndex) ∈
        referenceClause.literals.zipIdx)
    (translatedLiteralMember :
      (translatedLiteral, translatedLiteralIndex) ∈
        translatedClause.literals.zipIdx)
    (referenceChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula referenceClauseIndex referenceLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let referenceRoute :=
      finalCoordinatedSourceRoutes
        formula referenceClauseIndex referenceLiteralIndex
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula translatedClauseIndex translatedLiteralIndex)
    let terminal :=
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (classifiedRetainedTerminalData (routeTerminalVector referenceRoute))
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula referenceLiteral referenceClauseIndex referenceLiteralIndex
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline retainedAngularFanSourceClearanceFactor
          translatedRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            referenceRoute).getLastD (0, 0))) terminal slot) := by
  dsimp only
  let referenceRoute :=
    finalCoordinatedSourceRoutes
      formula referenceClauseIndex referenceLiteralIndex
  let translatedRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula translatedClauseIndex translatedLiteralIndex)
  let referenceTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector referenceRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor referenceTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula referenceLiteral referenceClauseIndex referenceLiteralIndex
  have referenceLength : 2 ≤ referenceRoute.length := by
    simpa [referenceRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have referenceClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector referenceRoute) = some referenceTerminal := by
    simpa [referenceRoute, referenceTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have aligned :
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    simpa [referenceRoute] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
        referenceChoiceNone
  have finalSegmentAvoid :=
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackFinalSegment_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty referenceClauseMember translatedClauseMember
      referenceLiteralMember translatedLiteralMember
      relativeTranslate relativeTranslateNonzero
  exact
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerCompleteRoute_of_axisAligned
      retainedAngularFanSourceClearanceFactor_gt_one
      translatedRoute referenceRoute referenceTerminal slot
      referenceLength referenceClassified aligned
      (by simpa [translatedRoute, referenceRoute] using finalSegmentAvoid)

/-- The fully refined translated fallback prefix avoids the delayed-lane
outer replacement of another fallback. -/
theorem
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_escapedFallbackOuter_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {referenceClause translatedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceClauseIndex translatedClauseIndex : Nat}
    (referenceClauseMember :
      (referenceClause, referenceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (translatedClauseMember :
      (translatedClause, translatedClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {referenceLiteral translatedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceLiteralIndex translatedLiteralIndex : Nat}
    (referenceLiteralMember :
      (referenceLiteral, referenceLiteralIndex) ∈
        referenceClause.literals.zipIdx)
    (translatedLiteralMember :
      (translatedLiteral, translatedLiteralIndex) ∈
        translatedClause.literals.zipIdx)
    (referenceChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula referenceClauseIndex referenceLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let referenceRoute :=
      finalCoordinatedSourceRoutes
        formula referenceClauseIndex referenceLiteralIndex
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula translatedClauseIndex translatedLiteralIndex)
    let terminal :=
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (classifiedRetainedTerminalData (routeTerminalVector referenceRoute))
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula referenceLiteral referenceClauseIndex referenceLiteralIndex
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline retainedAngularFanSourceClearanceFactor
          translatedRoute)).dropLast
      (retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            referenceRoute).getLastD (0, 0))) terminal slot) := by
  dsimp only
  let referenceRoute :=
    finalCoordinatedSourceRoutes
      formula referenceClauseIndex referenceLiteralIndex
  let translatedRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula translatedClauseIndex translatedLiteralIndex)
  let referenceTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector referenceRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor referenceTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula referenceLiteral referenceClauseIndex referenceLiteralIndex
  have referenceLength : 2 ≤ referenceRoute.length := by
    simpa [referenceRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have referenceClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector referenceRoute) = some referenceTerminal := by
    simpa [referenceRoute, referenceTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, referenceTerminal, referenceRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
  have aligned :
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    simpa [referenceRoute] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty referenceClauseMember referenceLiteralMember
        referenceChoiceNone
  have finalSegmentAvoid :=
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackFinalSegment_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty referenceClauseMember translatedClauseMember
      referenceLiteralMember translatedLiteralMember
      relativeTranslate relativeTranslateNonzero
  exact
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerEscapedCompleteRoute_of_axisAligned
      retainedAngularFanSourceClearanceFactor_gt_one
      translatedRoute referenceRoute referenceTerminal slot
      referenceLength referenceClassified escapeFits aligned
      (by simpa [translatedRoute, referenceRoute] using finalSegmentAvoid)

/-- A fully refined translated failed-choice source prefix avoids the
policy-selected outer replacement of another failed-choice source route at
every nonzero relative period. -/
theorem
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackOuterReplacement_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {referenceClause translatedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceClauseIndex translatedClauseIndex : Nat}
    (referenceClauseMember :
      (referenceClause, referenceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (translatedClauseMember :
      (translatedClause, translatedClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {referenceLiteral translatedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {referenceLiteralIndex translatedLiteralIndex : Nat}
    (referenceLiteralMember :
      (referenceLiteral, referenceLiteralIndex) ∈
        referenceClause.literals.zipIdx)
    (translatedLiteralMember :
      (translatedLiteral, translatedLiteralIndex) ∈
        translatedClause.literals.zipIdx)
    (referenceChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula referenceClauseIndex referenceLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula translatedClauseIndex translatedLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline retainedAngularFanSourceClearanceFactor
          translatedRoute)).dropLast
      (retainedFinalCoordinatedFallbackOuterReplacement
        formula referenceLiteral
        referenceClauseIndex referenceLiteralIndex) := by
  dsimp only
  let referenceRoute :=
    finalCoordinatedSourceRoutes
      formula referenceClauseIndex referenceLiteralIndex
  have ordinaryAvoid :=
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_ordinaryFallbackOuter_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty referenceClauseMember translatedClauseMember
      referenceLiteralMember translatedLiteralMember
      referenceChoiceNone
      relativeTranslate relativeTranslateNonzero
  have escapedAvoid :=
    retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_escapedFallbackOuter_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty referenceClauseMember translatedClauseMember
      referenceLiteralMember translatedLiteralMember referenceChoiceNone
      relativeTranslate relativeTranslateNonzero
  unfold retainedFinalCoordinatedFallbackOuterReplacement
  dsimp only
  by_cases singletonPrefix : referenceRoute.dropLast.length = 1
  · rw [if_pos (by simpa [referenceRoute] using singletonPrefix)]
    simpa [referenceRoute] using escapedAvoid
  · rw [if_neg (by simpa [referenceRoute] using singletonPrefix)]
    simpa [referenceRoute] using ordinaryAvoid

end PeriodicOrthocrossing
end LeanTrominoes
