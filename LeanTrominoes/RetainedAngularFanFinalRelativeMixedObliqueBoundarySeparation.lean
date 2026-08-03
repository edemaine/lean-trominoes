import LeanTrominoes.RetainedAngularFanFinalRelativeMixedObliqueTerminalSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeRoutedClausePrefixSeparation

/-!
# Relative oblique mixed boundary separation

Strict separation of the two discarded final-segment rectangles scales to
the radius-288 envelopes containing the direct replacement and translated
fallback outer replacement.  Combining this outer certificate with nonzero
translated source-prefix separation gives separation from the complete
fallback boundary prefix.
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

/-- The complete oblique direct replacement strictly avoids the translated
failed-choice outer replacement at distinct physical target centers. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_directSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
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
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedFinalTranslatedFallbackOuterReplacement
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (GridSegment.mk
              (polylineLastEntrance translatedFallbackRoute)
              (translatedFallbackRoute.getLastD (0, 0))).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (GridSegment.mk
              (polylineLastEntrance translatedFallbackRoute)
              (translatedFallbackRoute.getLastD (0, 0))).coordinateUpper))
  · intro point pointMember
    simpa [retainedAngularFanSourceClearanceFactor] using
      choice.completeRoute_point_in_sourceSegmentRectangle
        directSlot pointMember
  · intro point pointMember
    exact
      retainedFinalTranslatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember
        fallbackLiteralMember relativeTranslate pointMember
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        (retainedFinalDirectTranslatedFallback_finalSegmentRectanglesSeparated_of_directSegment_not_axisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          fallbackChoiceNone directOblique relativeTranslate
          centersDifferent)
        (by native_decide) (by native_decide)

/-- The complete oblique direct replacement strictly avoids the translated
failed-choice boundary prefix at nonzero shift and distinct physical target
centers. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_directSegment_not_axisAligned
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
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
  apply
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate
      (choice.completeRoute directSlot)
  · have prefixAvoid :=
      retainedFinalTranslatedFallbackSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directSlot relativeTranslate
        relativeTranslateNonzero
    dsimp only
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat]
    simpa only [directSlot, translatedRawRoute,
      retainedAngularFanSourceClearanceFactor,
      Nat.cast_ofNat] using prefixAvoid.symm
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_directSegment_not_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directSlot
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directOblique relativeTranslate centersDifferent

/-- A point in the second of two strictly separated closed rectangles cannot
also lie in the first. -/
private theorem not_in_firstClosedGridRectangle_of_separated_of_in_second
    {firstLower firstUpper secondLower secondUpper point : Cell}
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper)
    (inSecond :
      InClosedGridRectangle secondLower secondUpper point) :
    ¬InClosedGridRectangle firstLower firstUpper point := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [ClosedGridRectanglesSeparated] at separated
  simp only [InClosedGridRectangle] at inSecond ⊢
  omega

/-- The finish of the second segment is outside the first segment's endpoint
rectangle whenever the two endpoint rectangles are strictly separated. -/
private theorem point_outside_firstSegmentRectangle_of_separated_of_secondFinish_eq
    (first second : GridSegment) (point : Cell)
    (separated :
      ClosedGridRectanglesSeparated
        first.coordinateLower first.coordinateUpper
        second.coordinateLower second.coordinateUpper)
    (finishEq : second.finish = point) :
    ¬InClosedGridRectangle
      first.coordinateLower first.coordinateUpper point := by
  rw [← finishEq]
  exact
    not_in_firstClosedGridRectangle_of_separated_of_in_second
      separated second.finish_in_coordinateRectangle

/-- The endpoint of a translated final source route is its translated
canonical literal position. -/
private theorem translatedFinalCoordinatedSourceRoute_getLastD_eq
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
    (translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex)).getLastD (0, 0) =
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate) := by
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have endpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have routeNonempty : route ≠ [] := by
    intro routeNil
    rw [routeNil] at routeLength
    simp at routeLength
  change
    (translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      route).getLastD (0, 0) = _
  rw [translatePolyline_getLastD _ route routeNonempty,
    List.getLastD_eq_getLast?, endpoints.2]
  simp [Cell.add, add_comm]

/-- Package the final segment of a route behind a small interface before
using rectangle separation to exclude its endpoint from another segment. -/
private theorem routeFinish_outside_segmentRectangle_of_finalSegmentSeparated
    (segment : GridSegment) (route : List Cell) (point : Cell)
    (separated :
      ClosedGridRectanglesSeparated
        segment.coordinateLower segment.coordinateUpper
        (GridSegment.mk
          (polylineLastEntrance route)
          (route.getLastD (0, 0))).coordinateLower
        (GridSegment.mk
          (polylineLastEntrance route)
          (route.getLastD (0, 0))).coordinateUpper)
    (finishEq : route.getLastD (0, 0) = point) :
    ¬InClosedGridRectangle
      segment.coordinateLower segment.coordinateUpper point := by
  exact
    point_outside_firstSegmentRectangle_of_separated_of_secondFinish_eq
      segment
      (GridSegment.mk
        (polylineLastEntrance route)
        (route.getLastD (0, 0)))
      point separated finishEq

/-- At distinct physical target centers, the translated fallback target lies
outside the endpoint rectangle of an oblique direct source segment. -/
theorem
    retainedFinalCoordinatedObliqueDirectSourceSegment_translatedCanonicalLiteralPosition_outsideRectangle_of_distinctCenter
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
    ¬InClosedGridRectangle
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
        ((finalCoordinatedPlacement formula).translation
      relativeTranslate)) := by
  exact
    routeFinish_outside_segmentRectangle_of_finalSegmentSeparated
      choice.sourceSegment
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
      (Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate))
      (retainedFinalDirectTranslatedFallback_finalSegmentRectanglesSeparated_of_directSegment_not_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directOblique relativeTranslate centersDifferent)
      (translatedFinalCoordinatedSourceRoute_getLastD_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
        relativeTranslate)

/-- The complete oblique direct replacement strictly avoids the translated
fallback occurrence suffix at distinct physical target centers. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_distinctCenter
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
    let fallbackSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        fallbackSuffix) := by
  exact
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_centerOutside
      formula choice directLiteral directClauseIndex directLiteralIndex
      fallbackClause fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
      relativeTranslate
      (retainedFinalCoordinatedObliqueDirectSourceSegment_translatedCanonicalLiteralPosition_outsideRectangle_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directOblique relativeTranslate centersDifferent)

end PeriodicOrthocrossing
end LeanTrominoes
