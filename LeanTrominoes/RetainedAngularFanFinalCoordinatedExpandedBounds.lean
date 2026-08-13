/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalSourceScaledExpandedBounds
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation

/-!
# Expanded-period bounds for the final coordinated fixed-eight routes

The coordinated router changes only copied source incidences.  A successful
direct choice stays in a fixed-radius expansion of its represented retained
source segment.  The one exceptional failed choice uses the delayed-lane
escaped splice, whose generic expanded-period bound was proved alongside the
ordinary splice.  Appended implication-cycle routes remain unchanged.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A point in the radius-288 expansion of a fully refined source segment
inherits the source segment's strict neighboring-period bound. -/
private theorem point_inExpanded_of_in_fixedEightSourceSegmentRectangle
    {period : Nat}
    {segment : GridSegment}
    {point : Cell}
    (startBounded :
      -(period : Int) < segment.start.1 ∧
        segment.start.1 < 2 * period ∧
        -(period : Int) < segment.start.2 ∧
        segment.start.2 < 2 * period)
    (finishBounded :
      -(period : Int) < segment.finish.1 ∧
        segment.finish.1 < 2 * period ∧
        -(period : Int) < segment.finish.2 ∧
        segment.finish.2 < 2 * period)
    (pointBounded :
      InClosedGridRectangle
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            segment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            segment.coordinateUpper))
        point) :
    let refinedPeriod : Int :=
      (retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor) * period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.coordinateLower, GridSegment.coordinateUpper,
    InClosedGridRectangle, coordinateRadiusLower,
    coordinateRadiusUpper, Cell.scale] at pointBounded
  dsimp only [GridSegment.start, GridSegment.finish] at startBounded finishBounded
  dsimp only
  norm_num [retainedTerminalFanTotalRefinement_eq,
    retainedAngularFanSourceClearanceFactor,
    Nat.cast_mul] at pointBounded ⊢
  simp only [min_def, max_def] at pointBounded
  omega

/-- The delayed-lane fallback for a genuine copied source incidence remains
in the public fixed-eight open neighboring-period square. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_point_inExpanded
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
    {point : Cell}
    (pointMember :
      point ∈
        retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) :
    let refinedPeriod : Int :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let terminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector route)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have retained : RetainedRayPolyline route := by
    simpa [route] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor terminal) := by
    simpa [route, terminal] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeBounded :
      ∀ routePoint ∈ route,
        let sourcePeriod : Int :=
          (finalCoordinatedPlacement formula).period;
        -sourcePeriod < routePoint.1 ∧
          routePoint.1 < 2 * sourcePeriod ∧
          -sourcePeriod < routePoint.2 ∧
          routePoint.2 < 2 * sourcePeriod := by
    intro routePoint routePointMember
    exact
      finalCoordinatedSourceRoutes_point_inExpanded
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        routePointMember
  unfold retainedFinalEscapedFallbackOccurrenceRoute at pointMember
  dsimp only at pointMember
  rcases mem_joinAtEndpoint pointMember with
    boundaryMember | suffixMember
  · have bounded :=
      retainedAngularFanSourceScaledEscapedSplicedBoundaryRoute_point_inExpanded
        retainedAngularFanSourceClearanceFactor_pos
        (by
          norm_num [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor])
        route terminal slot routeLength classified retained
        escapeFits routeBounded boundaryMember
    simpa only [
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq,
      Nat.cast_mul] using bounded
  · have routeLast :=
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
    have centerMember :
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal ∈
          route := by
      exact mem_of_getLast?_eq_some (by simpa [route] using routeLast)
    have sourceCenterBounded :=
      routeBounded
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
        centerMember
    have scaledCenterBounded :
      let sourcePeriod : Int :=
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor).period;
      let center :=
        PositionedPeriodicCNF.canonicalLiteralPosition
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal;
      -sourcePeriod < center.1 ∧
        center.1 < 2 * sourcePeriod ∧
        -sourcePeriod < center.2 ∧
        center.2 < 2 * sourcePeriod := by
      rcases centerEq :
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal with
        ⟨centerX, centerY⟩
      simp only [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        PeriodicVariablePlacement.scale_period,
        centerEq, Cell.scale]
      simp only [centerEq] at sourceCenterBounded
      norm_num [retainedAngularFanSourceClearanceFactor,
        Nat.cast_mul] at sourceCenterBounded ⊢
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor <;> nlinarith
    have bounded :=
      scaledAngularOccurrenceSuffix_point_inExpanded
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor)
        (angularOccurrenceOrder
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes formula)))
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex scaledCenterBounded suffixMember
    have suffixPeriodEq :
        (retainedTerminalFanRoutingRefinement *
            PeriodicEightOccurrenceSplitPositioned.refinementScale) *
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor).period =
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).period := by
      rw [
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq,
        PeriodicVariablePlacement.scale_period]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedAngularFanSourceClearanceFactor]
      ring
    simpa only [suffixPeriodEq] using bounded

/-- A successful coordinated direct route remains in the public fixed-eight
open neighboring-period square. -/
theorem retainedFinalDirectCompleteFigure7Route_point_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    {point : Cell}
    (pointMember :
      point ∈ choice.completeFigure7Route
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)) :
    let refinedPeriod : Int :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have reverseTailRaw :
      ∃ entrance, route.reverse.tail.head? = some entrance :=
    exists_reverse_tail_head?_of_two_le_length route routeLength
  have entranceMember : polylineLastEntrance route ∈ route := by
    have entranceLast :
        route.dropLast.getLast? =
          some (polylineLastEntrance route) :=
      dropLast_getLast?_of_reverse_tail_head?
        (polylineLastEntrance_spec reverseTailRaw)
    exact List.mem_of_mem_dropLast
      (mem_of_getLast?_eq_some entranceLast)
  have routeNonempty : route ≠ [] := by
    intro routeEmpty
    rw [routeEmpty] at routeLength
    simp at routeLength
  have targetMember : route.getLastD (0, 0) ∈ route := by
    exact getLastD_mem_of_ne_nil route routeNonempty (0, 0)
  have entranceBounded :=
    finalCoordinatedSourceRoutes_point_inExpanded
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember entranceMember
  have targetBounded :=
    finalCoordinatedSourceRoutes_point_inExpanded
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember targetMember
  have segmentEq :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment) =
        choice.sourceSegment := by
    simpa [route] using
      retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
        formula clauseIndex literalIndex choice choiceLookup
  have localBound :=
    choice.completeFigure7Route_point_in_sourceSegmentRectangle
      (retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex)
      pointMember
  have bounded :=
    point_inExpanded_of_in_fixedEightSourceSegmentRectangle
      (segment :=
        ⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩)
      entranceBounded targetBounded
      (by
        rw [segmentEq]
        exact localBound)
  simpa only [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq,
    Nat.cast_mul] using bounded

/-- Every point of every genuine route in the final coordinated fixed-eight
drawing lies in the open neighboring-period square of its public refined
placement. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) :
    let refinedPeriod : Int :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  have publicClauseMember := clauseMember
  have publicLiteralMember := literalMember
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual : baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement = clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale retainedAngularFanSourceClearanceFactor
  let placement :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
  let order := angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      baseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        baseClause =
          occurrenceClause occurrencePorts baseIndex
            metadata.sourceClause := by
      calc
        baseClause = metadata.clause := metadataClauseEqual.symm
        _ = occurrenceClause occurrencePorts metadata.clauseIndex
              metadata.sourceClause := metadataClauseDefinition
        _ = occurrenceClause occurrencePorts baseIndex
              metadata.sourceClause := by rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual baseLiteralMember with
      ⟨sourceLiteral, sourceLiteralMember, _copiedLiteralEqual⟩
    dsimp only [source] at sourceClauseMemberAt
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at sourceClauseMemberAt
    rcases List.mem_map.mp sourceClauseMemberAt with
      ⟨rawTaggedClause, rawTaggedClauseMember,
        rawTaggedClauseEqual⟩
    rcases rawTaggedClause with ⟨rawClause, rawIndex⟩
    have rawIndexEqual : rawIndex = baseIndex :=
      congrArg Prod.snd rawTaggedClauseEqual
    have rawScaledClauseEqual :
        rawClause.scale retainedAngularFanSourceClearanceFactor =
          metadata.sourceClause :=
      congrArg Prod.fst rawTaggedClauseEqual
    subst rawIndex
    have rawLiteralMember :
        (sourceLiteral, literalIndex) ∈
          rawClause.literals.zipIdx := by
      have scaledLiteralMember :
          (sourceLiteral, literalIndex) ∈
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor).literals.zipIdx := by
        rw [rawScaledClauseEqual]
        exact sourceLiteralMember
      simpa using scaledLiteralMember
    have rawClauseMember :
        (rawClause, baseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx := by
      simpa only [finalCoordinatedSource] using rawTaggedClauseMember
    cases choiceLookup :
        retainedFinalDirectSourceRouteChoice?
          formula baseIndex literalIndex with
    | none =>
        by_cases prefixLength :
            (finalCoordinatedSourceRoutes
              formula baseIndex literalIndex).dropLast.length = 1
        · have routeEq :=
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty rawClauseMember rawLiteralMember
              choiceLookup
          rw [routeEq, retainedFinalFallbackOccurrenceRoute,
            if_pos prefixLength] at pointMember
          exact
            retainedFinalEscapedFallbackOccurrenceRoute_point_inExpanded
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty rawClauseMember rawLiteralMember
              pointMember
        · rw [
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
              formula baseIndex literalIndex choiceLookup prefixLength]
            at pointMember
          exact
            retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty publicClauseMember
              publicLiteralMember pointMember
    | some choice =>
        have routeEq :=
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty choice rawClauseMember
            rawLiteralMember choiceLookup
        rw [routeEq] at pointMember
        exact
          retainedFinalDirectCompleteFigure7Route_point_inExpanded
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty choice rawClauseMember
            rawLiteralMember choiceLookup pointMember
  · have sourceIndexGe :
        source.clauses.length ≤ baseIndex := by
      simpa [PeriodicEightOccurrenceSplitPositioned.occurrenceClauses,
        source] using occurrenceIndex
    have scaledClauseNone :
        finalCoordinatedScaledClause? formula baseIndex = none := by
      exact List.getElem?_eq_none_iff.mpr
        (by
          simpa [source, finalCoordinatedSource] using sourceIndexGe)
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_clause_none
        formula baseIndex literalIndex scaledClauseNone] at pointMember
    exact
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty publicClauseMember
        publicLiteralMember pointMember

end PeriodicOrthocrossing
end LeanTrominoes
