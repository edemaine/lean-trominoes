import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSameCenterBoundarySeparation

/-!
# Distinct-center translated fallback boundary separation

At different physical variable targets, relative source-route separation
separates the discarded terminal-segment rectangles.  The conservative
outer-fan bounds lift that fact through both refinements and both singleton
policies.  The remaining prefix interactions are the center-independent
ones, so the two selected fallback boundaries can then be assembled.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Distinct targets and nonzero relative source planarity separate the two
discarded terminal-segment rectangles. -/
theorem
    retainedFinalFallbackTranslatedFallback_finalSegmentRectanglesSeparated_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    let firstRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let translatedSecondRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)
    ClosedGridRectanglesSeparated
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
      (⟨polylineLastEntrance translatedSecondRoute,
          translatedSecondRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance translatedSecondRoute,
          translatedSecondRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper := by
  dsimp only
  let firstRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      secondRoute
  have firstLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondLength : 2 ≤ translatedSecondRoute.length := by
    simpa [translatedSecondRoute, translatePolyline] using secondLength
  have firstOrthogonal : OrthogonalPolyline firstRoute := by
    simpa [firstRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        firstChoiceNone
  have secondOrthogonal : OrthogonalPolyline secondRoute := by
    simpa [secondRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondChoiceNone
  have translatedSecondOrthogonal :
      OrthogonalPolyline translatedSecondRoute :=
    secondOrthogonal.translate
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
  have firstAligned :
      (⟨polylineLastEntrance firstRoute,
          firstRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned :=
    (orthogonalPolyline_iff_segments firstRoute).mp firstOrthogonal _
      (finalGridSegment_mem firstRoute firstLength)
  have secondAligned :
      (⟨polylineLastEntrance translatedSecondRoute,
          translatedSecondRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned :=
    (orthogonalPolyline_iff_segments translatedSecondRoute).mp
      translatedSecondOrthogonal _
      (finalGridSegment_mem translatedSecondRoute translatedSecondLength)
  have strict :
      RoutesStrictlyAvoidEachOther firstRoute translatedSecondRoute := by
    simpa [firstRoute, secondRoute, translatedSecondRoute] using
      finalCoordinatedSourceRoutes_strictlyAvoid_translated_of_nonzero_of_distinctCenters
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate
        relativeTranslateNonzero centersDifferent
  simpa [firstRoute, secondRoute, translatedSecondRoute] using
    finalSegment_coordinateRectanglesSeparated_of_strictlyAvoid
      firstLength translatedSecondLength firstAligned secondAligned strict

/-- At distinct translated targets, the two policy-selected outer
replacements are strictly separated. -/
theorem
    retainedFinalCoordinatedFallbackOuterReplacement_strictlyAvoids_translated_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackOuterReplacement
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOuterReplacement
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let firstRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula secondClauseIndex secondLiteralIndex)
  have rectanglesSeparated :=
    retainedFinalFallbackTranslatedFallback_finalSegmentRectanglesSeparated_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember firstChoiceNone secondChoiceNone
      relativeTranslate relativeTranslateNonzero centersDifferent
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance translatedSecondRoute,
                translatedSecondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (⟨polylineLastEntrance translatedSecondRoute,
                translatedSecondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
  · intro point pointMember
    simpa [firstRoute] using
      retainedFinalCoordinatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember pointMember
  · intro point pointMember
    simpa [translatedSecondRoute] using
      retainedFinalTranslatedFallbackOuterReplacement_point_in_scaledFinalSegmentRectangle
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        relativeTranslate pointMember
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        (by simpa [firstRoute, translatedSecondRoute] using rectanglesSeparated)
        (by native_decide) (by native_decide)

/-- At distinct physical targets, the two selected fallback boundaries are
strictly separated across a nonzero period shift. -/
theorem
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_translated_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let firstPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex))).dropLast
  let translatedSecondPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex)))).dropLast
  let firstOuter :=
    retainedFinalCoordinatedFallbackOuterReplacement
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let translatedSecondOuter :=
    retainedFinalTranslatedFallbackOuterReplacement
      formula secondLiteral secondClauseIndex secondLiteralIndex
      relativeTranslate
  have prefixesAvoid :
      RoutesStrictlyAvoidEachOther firstPrefix translatedSecondPrefix := by
    have unscaled :=
      finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate
        relativeTranslateNonzero
    have scaled := unscaled.scalePolyline
      (factor :=
        ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor : Nat) : Int))
      (by
        norm_num [retainedTerminalFanTotalRefinement_eq,
          retainedAngularFanSourceClearanceFactor_eq])
    rw [← scalePolyline_dropLast_eq,
      ← scalePolyline_dropLast_eq] at scaled
    dsimp only [firstPrefix, translatedSecondPrefix]
    rw [scalePolyline_scalePolyline_nat,
      scalePolyline_scalePolyline_nat]
    exact scaled
  have firstPrefixAvoidSecondOuter :
      RoutesStrictlyAvoidEachOther firstPrefix translatedSecondOuter := by
    simpa [firstPrefix, translatedSecondOuter] using
      retainedFinalFallbackSourcePrefix_strictlyAvoids_translatedFallbackOuterReplacement_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember secondChoiceNone
        relativeTranslate relativeTranslateNonzero
  have secondPrefixAvoidFirstOuter :
      RoutesStrictlyAvoidEachOther translatedSecondPrefix firstOuter := by
    simpa [translatedSecondPrefix, firstOuter] using
      retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackOuterReplacement_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        relativeTranslate relativeTranslateNonzero
  have outersAvoid :
      RoutesStrictlyAvoidEachOther firstOuter translatedSecondOuter := by
    simpa [firstOuter, translatedSecondOuter] using
      retainedFinalCoordinatedFallbackOuterReplacement_strictlyAvoids_translated_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersDifferent
  have firstPrefixAvoidSecondBoundary :=
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      secondChoiceNone relativeTranslate firstPrefix
      (by simpa [translatedSecondPrefix] using prefixesAvoid)
      (by simpa [translatedSecondOuter] using firstPrefixAvoidSecondOuter)
  have firstOuterAvoidSecondBoundary :=
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      secondChoiceNone relativeTranslate firstOuter
      (by simpa [translatedSecondPrefix] using
        secondPrefixAvoidFirstOuter.symm)
      (by simpa [translatedSecondOuter] using outersAvoid)
  exact
    (strictlyAvoids_retainedFinalCoordinatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstChoiceNone
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate)
      (by simpa [firstPrefix] using firstPrefixAvoidSecondBoundary.symm)
      (by simpa [firstOuter] using firstOuterAvoidSecondBoundary.symm)).symm

end PeriodicOrthocrossing
end LeanTrominoes
