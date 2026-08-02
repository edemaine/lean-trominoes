import LeanTrominoes.RetainedAngularFanFinalMixedFallbackSuffixSeparation
import LeanTrominoes.RetainedAngularFanMixedBoundaryAssembly
import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation

/-!
# Selected fallback-boundary assembly

The final coordinated router chooses between the ordinary outer fan and the
delayed-lane escaped outer fan according to whether the unscaled retained
source prefix is a singleton.  This file packages the same choice for the
outer replacement and lifts the generic two-piece boundary assembly theorem
to the final router.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- The outer replacement selected for a failed final direct-source lookup.
It uses exactly the same singleton-prefix test as the selected fallback
boundary. -/
def retainedFinalCoordinatedFallbackOuterReplacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) : List Cell :=
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute))
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  if rawRoute.dropLast.length = 1 then
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  else
    retainedTerminalFanOuterCompleteRoute
      center terminal slot

/-- The router-selected fallback replacement stays in the same conservative
radius-288 expansion of its discarded source-segment rectangle in both the
ordinary and delayed-lane cases. -/
theorem
    retainedFinalCoordinatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
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
      point ∈ retainedFinalCoordinatedFallbackOuterReplacement
        formula literal clauseIndex literalIndex) :
    let route :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper))
      point := by
  dsimp only
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
  have routeClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal] using
      finalCoordinatedSourceRoute_classified
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
  unfold retainedFinalCoordinatedFallbackOuterReplacement at pointMember
  dsimp only at pointMember
  by_cases singletonPrefix : route.dropLast.length = 1
  · rw [if_pos (by simpa [route] using singletonPrefix)] at pointMember
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        route terminal slot routeLength routeClassified escapeFits pointMember
  · rw [if_neg (by simpa [route] using singletonPrefix)] at pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        route terminal slot routeLength routeClassified pointMember

/-- If the discarded source-segment rectangles are already separated, a
selected direct route strictly avoids the router-selected fallback outer
replacement. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalCoordinatedFallbackOuterReplacement_of_finalSegmentRectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    {fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackClauseIndex : Nat}
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackLiteralIndex : Nat}
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (rectanglesSeparated :
      let fallbackRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      ClosedGridRectanglesSeparated
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (⟨polylineLastEntrance fallbackRoute,
            fallbackRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance fallbackRoute,
            fallbackRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedFinalCoordinatedFallbackOuterReplacement
        formula fallbackLiteral
        fallbackClauseIndex fallbackLiteralIndex) := by
  dsimp only at rectanglesSeparated
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
            (⟨polylineLastEntrance
                (finalCoordinatedSourceRoutes formula
                  fallbackClauseIndex fallbackLiteralIndex),
              (finalCoordinatedSourceRoutes formula
                fallbackClauseIndex fallbackLiteralIndex).getLastD
                  (0, 0)⟩ : GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance
                (finalCoordinatedSourceRoutes formula
                  fallbackClauseIndex fallbackLiteralIndex),
              (finalCoordinatedSourceRoutes formula
                fallbackClauseIndex fallbackLiteralIndex).getLastD
                  (0, 0)⟩ : GridSegment).coordinateUpper))
  · intro point pointMember
    simpa [retainedAngularFanSourceClearanceFactor] using
      choice.completeRoute_point_in_sourceSegmentRectangle
        directSlot pointMember
  · intro point pointMember
    exact
      retainedFinalCoordinatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember
        fallbackLiteralMember pointMember
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        rectanglesSeparated (by native_decide) (by native_decide)

/-- Avoiding the fully refined retained source prefix and the selected outer
replacement suffices to avoid the actual selected fallback boundary. -/
theorem
    strictlyAvoids_retainedFinalCoordinatedFallbackBoundaryPrefix_of_pieces
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
    (other : List Cell)
    (prefixAvoid :
      RoutesStrictlyAvoidEachOther other
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex))).dropLast)
    (replacementAvoid :
      RoutesStrictlyAvoidEachOther other
        (retainedFinalCoordinatedFallbackOuterReplacement
          formula literal clauseIndex literalIndex)) :
    RoutesStrictlyAvoidEachOther other
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula literal clauseIndex literalIndex) := by
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
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
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix, if_pos]
    apply
      strictlyAvoids_retainedAngularFanEscapedSplicedBoundaryRoute_of_prefix_replacement
        other route terminal slot routeLength routeClassified
        routeOrthogonal escapeFits
    · simpa [route, rawRoute] using prefixAvoid
    · unfold retainedFinalCoordinatedFallbackOuterReplacement at replacementAvoid
      dsimp only at replacementAvoid
      rw [if_pos (by simpa [rawRoute] using singletonPrefix)] at replacementAvoid
      simpa [route, terminal, rawTerminal, slot] using replacementAvoid
  · rw [retainedFinalCoordinatedFallbackBoundaryPrefix]
    simp only [rawRoute, singletonPrefix]
    apply
      strictlyAvoids_retainedAngularFanSplicedBoundaryRoute_of_prefix_replacement
        other route terminal slot routeLength routeClassified
        routeOrthogonal
    · simpa [route, rawRoute] using prefixAvoid
    · unfold retainedFinalCoordinatedFallbackOuterReplacement at replacementAvoid
      dsimp only at replacementAvoid
      rw [if_neg (by simpa [rawRoute] using singletonPrefix)] at replacementAvoid
      simpa [route, terminal, rawTerminal, slot] using replacementAvoid

end PeriodicOrthocrossing
end LeanTrominoes
