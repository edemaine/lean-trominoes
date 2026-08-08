import LeanTrominoes.RetainedAngularFanFinalCoordinatedExpandedBounds
import LeanTrominoes.RetainedAngularFanFinalSourceScaledRouteRadiusBounds

/-!
# Variable-centered radius bounds for coordinated fixed-eight routes

The public coordinated router replaces some copied-source routes by a
delayed-lane fallback or by a finite direct Figure 7 atlas route.  This
module bounds both replacements around the same copied variable endpoint as
the original route, then packages the total coordinated family with the
one-period rebased radius certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Expanding the uniformly scaled endpoint rectangle of a segment increases
a common endpoint-centered coordinate-radius bound by just the rectangle's
fixed expansion. -/
private theorem withinCoordinateRadius_of_in_segmentRectangle
    {expansion radius : Nat}
    {center : Cell} {segment : GridSegment} {point : Cell}
    (startBounded :
      WithinCoordinateRadius radius center segment.start)
    (finishBounded :
      WithinCoordinateRadius radius center segment.finish)
    (pointBounded :
      InClosedGridRectangle
        (coordinateRadiusLower expansion
          segment.coordinateLower)
        (coordinateRadiusUpper expansion
          segment.coordinateUpper)
        point) :
    WithinCoordinateRadius (radius + expansion)
      center point := by
  rcases center with ⟨centerX, centerY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  change
    WithinCoordinateRadius radius
      (centerX, centerY) (startX, startY)
    at startBounded
  change
    WithinCoordinateRadius radius
      (centerX, centerY) (finishX, finishY)
    at finishBounded
  rw [withinCoordinateRadius_iff_abs_le]
    at startBounded finishBounded ⊢
  simp only [GridSegment.coordinateLower, GridSegment.coordinateUpper,
    InClosedGridRectangle, coordinateRadiusLower,
    coordinateRadiusUpper,
    Nat.cast_add] at pointBounded ⊢
  simp only [min_def, max_def] at pointBounded
  rcases abs_le.mp startBounded.1 with
    ⟨startXLower, startXUpper⟩
  rcases abs_le.mp startBounded.2 with
    ⟨startYLower, startYUpper⟩
  rcases abs_le.mp finishBounded.1 with
    ⟨finishXLower, finishXUpper⟩
  rcases abs_le.mp finishBounded.2 with
    ⟨finishYLower, finishYUpper⟩
  constructor <;> apply abs_le.mpr <;> omega

/-- A successful direct Figure 7 route stays within the strict source-radius
budget plus the fixed 288-cell atlas margin and 48-cell copied-center shift. -/
theorem retainedFinalDirectCompleteFigure7Route_point_withinCopiedLiteralRadius
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
    let scaledSource :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let scaledPlacement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let scaledRoutes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder scaledSource.erase
        (angularOccurrenceOrder scaledSource.erase scaledRoutes)
    let copiedClause :=
      occurrenceClause occurrencePorts clauseIndex
        (clause.scale retainedAngularFanSourceClearanceFactor)
    let copiedLiteral :=
      PeriodicEightOccurrenceSplit.occurrenceLiteral
        occurrencePorts clauseIndex literalIndex literal
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor) *
          ((finalCoordinatedPlacement formula).period - 1) + 336)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (placement scaledPlacement)
          copiedClause copiedLiteral))
      point := by
  dsimp only
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let sourceCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula) clause literal
  let refinedSourceCenter :=
    Cell.scale
      (retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor)
      sourceCenter
  let scaledSource :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let scaledPlacement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let scaledRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order :=
    angularOccurrenceOrder scaledSource.erase scaledRoutes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder scaledSource.erase order
  let copiedCenter :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (placement scaledPlacement)
        (occurrenceClause occurrencePorts clauseIndex
          (clause.scale retainedAngularFanSourceClearanceFactor))
        (PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts clauseIndex literalIndex literal))
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourceBounds :=
    retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePredPeriod
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
  have routeBounded :
      ∀ routePoint ∈ route,
        WithinCoordinateRadius
          ((finalCoordinatedPlacement formula).period - 1)
          sourceCenter routePoint := by
    intro routePoint routePointMember
    exact
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius.rawRoutePointsWithinCanonicalLiteralRadius
        (by simpa [finalCoordinatedSource,
          finalCoordinatedPlacement,
          finalCoordinatedSourceRoutes] using sourceBounds)
        clauseMember literalMember
        (by simpa [route, finalCoordinatedSourceRoutes] using
          routePointMember)
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
  have targetMember : route.getLastD (0, 0) ∈ route :=
    getLastD_mem_of_ne_nil route routeNonempty (0, 0)
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
  have segmentEq : finalSegment = choice.sourceSegment := by
    simpa [finalSegment, route] using
      retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
        formula clauseIndex literalIndex choice choiceLookup
  have pointRectangle :
      InClosedGridRectangle
        (coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            finalSegment.coordinateLower))
        (coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            finalSegment.coordinateUpper))
        point := by
    rw [segmentEq]
    simpa [retainedAngularFanSourceClearanceFactor] using
      choice.completeFigure7Route_point_in_sourceSegmentRectangle
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)
        pointMember
  have sourceCentered :
      WithinCoordinateRadius
        ((retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor) *
            ((finalCoordinatedPlacement formula).period - 1) + 288)
        refinedSourceCenter point := by
    let refinedSegment :=
      finalSegment.scale
        (retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor)
    have refinedPointRectangle :
        InClosedGridRectangle
          (coordinateRadiusLower 288
            refinedSegment.coordinateLower)
          (coordinateRadiusUpper 288
            refinedSegment.coordinateUpper)
          point := by
      simpa [refinedSegment,
        GridSegment.coordinateLower_scale,
        GridSegment.coordinateUpper_scale] using pointRectangle
    exact
      withinCoordinateRadius_of_in_segmentRectangle
        (segment := refinedSegment)
        ((routeBounded _ entranceMember).scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor))
        ((routeBounded _ targetMember).scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor))
        refinedPointRectangle
  have copiedCenterFromScaledSource :=
    occurrenceLiteralPosition_within_scaledSourceLiteral
      scaledPlacement occurrencePorts clauseIndex literalIndex
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal
  have copiedCenterFromSource :
      WithinCoordinateRadius 48
        refinedSourceCenter copiedCenter := by
    have refined :=
      copiedCenterFromScaledSource.scale
        retainedTerminalFanRoutingRefinement
    have refinedCenterEq :
        Cell.scale retainedTerminalFanRoutingRefinement
            (Cell.scale refinementScale
              (PositionedPeriodicCNF.canonicalLiteralPosition
                scaledPlacement
                (clause.scale retainedAngularFanSourceClearanceFactor)
                literal)) =
          refinedSourceCenter := by
      rcases centerEq : sourceCenter with ⟨centerX, centerY⟩
      apply Prod.ext <;>
        simp [refinedSourceCenter, sourceCenter, scaledPlacement,
          PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
          Cell.scale_scale, retainedTerminalFanTotalRefinement_eq,
          retainedTerminalFanRoutingRefinement, refinementScale,
          retainedAngularFanSourceClearanceFactor,
          centerEq]
    rw [refinedCenterEq] at refined
    simpa [copiedCenter, retainedTerminalFanRoutingRefinement]
      using refined
  have recentered :=
    copiedCenterFromSource.symm.trans sourceCentered
  change
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor) *
          ((finalCoordinatedPlacement formula).period - 1) + 336)
      copiedCenter point
  exact recentered.mono (by omega)

/-- The delayed-lane fallback specializes the generic escaped-splice bound
to the final retained source and its strict one-cell radius margin. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_point_withinCopiedLiteralRadius
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
      point ∈ retainedFinalEscapedFallbackOccurrenceRoute
        formula
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex) :
    let scaledSource :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let scaledPlacement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let scaledRoutes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder scaledSource.erase
        (angularOccurrenceOrder scaledSource.erase scaledRoutes)
    let copiedClause :=
      occurrenceClause occurrencePorts clauseIndex
        (clause.scale retainedAngularFanSourceClearanceFactor)
    let copiedLiteral :=
      PeriodicEightOccurrenceSplit.occurrenceLiteral
        occurrencePorts clauseIndex literalIndex literal
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor) *
          ((finalCoordinatedPlacement formula).period - 1) + 345)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (placement scaledPlacement)
          copiedClause copiedLiteral))
      point := by
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let terminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector route)
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourceBounds :=
    retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePredPeriod
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
  have rawRouteBounded :
      ∀ routePoint ∈ route,
        WithinCoordinateRadius
          ((finalCoordinatedPlacement formula).period - 1)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal)
          routePoint := by
    intro routePoint routePointMember
    exact
      PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius.rawRoutePointsWithinCanonicalLiteralRadius
        (by simpa [finalCoordinatedSource,
          finalCoordinatedPlacement,
          finalCoordinatedSourceRoutes] using sourceBounds)
        clauseMember literalMember
        (by simpa [route, finalCoordinatedSourceRoutes] using
          routePointMember)
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeLength : 2 ≤ route.length := by
    simpa [route] using
      finalCoordinatedSourceRoutes_length_ge_two
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
  unfold retainedFinalEscapedFallbackOccurrenceRoute at pointMember
  dsimp only at pointMember
  have bounded :=
    retainedAngularFanSourceScaledEscapedSplicedOccurrenceRoute_point_withinCopiedLiteralRadius
      retainedAngularFanSourceClearanceFactor_pos
      (finalCoordinatedSource formula)
      (finalCoordinatedPlacement formula)
      (finalCoordinatedSourceRoutes formula)
      clauseMember literalMember terminal classified
      (by simpa [route] using routeLength)
      (by simpa [route] using retained)
      escapeFits
      (by simpa [route] using rawRouteBounded)
      (by simpa [route, terminal,
        retainedFinalCoordinatedOccurrenceSlot] using pointMember)
  simpa using bounded

/-- Every physical route point of the public coordinated fixed-eight family
lies within one public placement period of its canonical literal endpoint. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
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
    WithinCoordinateRadius
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula)
        clause literal)
      point := by
  have publicClauseMember := clauseMember
  have publicLiteralMember := literalMember
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
  let order := angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  have publicPeriodEq :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq
      formula
  have sourcePeriodPositive :
      0 < (finalCoordinatedPlacement formula).period := by
    simpa [finalCoordinatedPlacement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
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
  by_cases occurrenceIndex :
      baseIndex <
        (occurrenceClauses source occurrencePorts).length
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
      ⟨sourceLiteral, sourceLiteralMember,
        copiedLiteralEqual⟩
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
      simpa only [← rawScaledClauseEqual,
        PositionedPeriodicClause.scale_literals] using
        sourceLiteralMember
    have rawClauseMember :
        (rawClause, baseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx := by
      simpa only [finalCoordinatedSource] using
        rawTaggedClauseMember
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
          have bounded :=
            retainedFinalEscapedFallbackOccurrenceRoute_point_withinCopiedLiteralRadius
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty rawClauseMember rawLiteralMember
              pointMember
          have radiusLe :
              (retainedTerminalFanTotalRefinement *
                    retainedAngularFanSourceClearanceFactor) *
                    ((finalCoordinatedPlacement formula).period - 1) +
                  345 ≤
                (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                  formula).period := by
            rw [publicPeriodEq]
            norm_num [retainedTerminalFanTotalRefinement_eq,
              retainedAngularFanSourceClearanceFactor]
            omega
          have finalBounded := bounded.mono radiusLe
          simpa only [copiedClauseEqual, copiedLiteralEqual,
            ← rawScaledClauseEqual,
            retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
            retainedAngularFanSourceScaledRefinedPlacement,
            retainedAngularFanRefinedPlacement,
            source, placement, routes, order, occurrencePorts,
            finalCoordinatedPlacement,
            PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
            using finalBounded
        · rw [
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
              formula baseIndex literalIndex choiceLookup prefixLength]
            at pointMember
          exact
            retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
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
        have bounded :=
          retainedFinalDirectCompleteFigure7Route_point_withinCopiedLiteralRadius
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty choice rawClauseMember
            rawLiteralMember choiceLookup pointMember
        have radiusLe :
            (retainedTerminalFanTotalRefinement *
                  retainedAngularFanSourceClearanceFactor) *
                  ((finalCoordinatedPlacement formula).period - 1) +
                336 ≤
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula).period := by
          rw [publicPeriodEq]
          norm_num [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor]
          omega
        have finalBounded := bounded.mono radiusLe
        simpa only [copiedClauseEqual, copiedLiteralEqual,
          ← rawScaledClauseEqual,
          retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
          retainedAngularFanSourceScaledRefinedPlacement,
          retainedAngularFanRefinedPlacement,
          source, placement, routes, order, occurrencePorts,
          finalCoordinatedPlacement,
          PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
          using finalBounded
  · have sourceIndexGe : source.clauses.length ≤ baseIndex := by
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
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty publicClauseMember
        publicLiteralMember pointMember

/-- The public coordinated fixed-eight route family retains the complete
rebased one-period variable-radius certificate. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  apply
    PositionedPeriodicCNF.rebasedIncidenceRoutesWithinVariableRadius_of_rawRoutePointsWithinCanonicalLiteralRadius
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  exact
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember pointMember

end PeriodicOrthocrossing
end LeanTrominoes
