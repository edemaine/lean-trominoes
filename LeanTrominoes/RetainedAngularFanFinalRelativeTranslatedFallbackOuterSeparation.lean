import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSourceCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedBoundaryAssembly

/-!
# Translated fallback outer-fan separation

The failed-choice outer replacement is rebuilt after translating its retained
source route.  It remains inside the radius-288 expansion of the translated
discarded terminal segment.  Strict relative retained-source separation makes
that terminal rectangle disjoint from an aligned direct choice's represented
segment, so the two fully refined route envelopes are disjoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The policy-selected outer replacement rebuilt at the translated retained
source endpoint. -/
def retainedFinalTranslatedFallbackOuterReplacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell) : List Cell :=
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
      rawRoute
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      translatedRawRoute
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

/-- The translated selected outer replacement stays in the radius-288
expansion of its translated discarded source-segment rectangle. -/
theorem
    retainedFinalTranslatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
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
    (relativeTranslate : Cell)
    {point : Cell}
    (pointMember :
      point ∈ retainedFinalTranslatedFallbackOuterReplacement
        formula literal clauseIndex literalIndex relativeTranslate) :
    let translatedRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (⟨polylineLastEntrance translatedRoute,
              translatedRoute.getLastD (0, 0)⟩ :
            GridSegment).coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (⟨polylineLastEntrance translatedRoute,
              translatedRoute.getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper))
      point := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let translatedRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
      rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have translatedLength : 2 ≤ translatedRoute.length := by
    simpa [translatedRoute, translatePolyline] using rawLength
  have rawClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector rawRoute) = some rawTerminal := by
    simpa [rawRoute, rawTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have translatedClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector translatedRoute) = some rawTerminal := by
    simpa [translatedRoute, routeTerminalVector_translatePolyline] using
      rawClassified
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  unfold retainedFinalTranslatedFallbackOuterReplacement at pointMember
  dsimp only at pointMember
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [if_pos (by simpa [rawRoute] using singletonPrefix)] at pointMember
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        translatedRoute rawTerminal slot translatedLength
        translatedClassified escapeFits
        (by simpa [terminal, slot, translatedRoute, rawRoute] using pointMember)
  · rw [if_neg (by simpa [rawRoute] using singletonPrefix)] at pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        translatedRoute rawTerminal slot translatedLength
        translatedClassified
        (by simpa [terminal, slot, translatedRoute, rawRoute] using pointMember)

/-- The discarded source-segment rectangles of an aligned direct route and
a translated failed-choice route are separated at distinct canonical
centers. -/
theorem
    retainedFinalDirectTranslatedFallback_finalSegmentRectanglesSeparated_of_axisAligned
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
      (⟨polylineLastEntrance translatedFallbackRoute,
          translatedFallbackRoute.getLastD (0, 0)⟩ :
        GridSegment).coordinateLower
      (⟨polylineLastEntrance translatedFallbackRoute,
          translatedFallbackRoute.getLastD (0, 0)⟩ :
        GridSegment).coordinateUpper := by
  dsimp only
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
      fallbackRoute
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
  have representedSegment :
      (⟨polylineLastEntrance directRoute,
          directRoute.getLastD (0, 0)⟩ : GridSegment) =
        choice.sourceSegment := by
    simpa [directRoute] using
      retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have directFinalAligned :
      (⟨polylineLastEntrance directRoute,
          directRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
    rw [representedSegment]
    exact directAligned
  have fallbackOrthogonal : OrthogonalPolyline fallbackRoute := by
    simpa [fallbackRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember
        fallbackLiteralMember fallbackChoiceNone
  have translatedFallbackOrthogonal :
      OrthogonalPolyline translatedFallbackRoute := by
    exact fallbackOrthogonal.translate
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
  have translatedFallbackFinalAligned :
      (⟨polylineLastEntrance translatedFallbackRoute,
          translatedFallbackRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned :=
    (orthogonalPolyline_iff_segments translatedFallbackRoute).mp
      translatedFallbackOrthogonal
      (⟨polylineLastEntrance translatedFallbackRoute,
          translatedFallbackRoute.getLastD (0, 0)⟩ : GridSegment)
      (finalGridSegment_mem
        translatedFallbackRoute translatedFallbackLength)
  have strict :
      RoutesStrictlyAvoidEachOther
        directRoute translatedFallbackRoute := by
    simpa [directRoute, fallbackRoute, translatedFallbackRoute] using
      finalCoordinatedSourceRoutes_strictlyAvoid_translated_of_nonzero_of_distinctCenters
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero centersDifferent
  have separated :=
    finalSegment_coordinateRectanglesSeparated_of_strictlyAvoid
      directLength translatedFallbackLength
      directFinalAligned translatedFallbackFinalAligned strict
  rw [representedSegment] at separated
  exact separated

/-- The complete aligned direct source-to-boundary route strictly avoids the
selected translated failed-choice outer replacement. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_axisAligned
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
    (directAligned : choice.sourceSegment.IsAxisAligned)
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
      (choice.completeRoute directSlot)
      (retainedFinalTranslatedFallbackOuterReplacement
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
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
            (⟨polylineLastEntrance translatedFallbackRoute,
                translatedFallbackRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance translatedFallbackRoute,
                translatedFallbackRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
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
        (retainedFinalDirectTranslatedFallback_finalSegmentRectanglesSeparated_of_axisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          fallbackChoiceNone directAligned relativeTranslate
          relativeTranslateNonzero centersDifferent)
        (by native_decide) (by native_decide)

end PeriodicOrthocrossing
end LeanTrominoes
