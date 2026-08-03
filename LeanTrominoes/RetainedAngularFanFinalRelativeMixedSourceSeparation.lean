import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSourceModels
import LeanTrominoes.RetainedFinalSourceRouteOtherTranslatedTargetSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherSpokeSeparation

/-!
# Relative mixed source-route separation

This file begins the periodic direct/fallback branch by separating a direct
source-to-boundary route from a translated Figure 7 occurrence suffix.  The
translated suffix retains its uniform radius-96 center bound, so the existing
direct-atlas source-segment envelope applies unchanged.
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

/-- For an axis-aligned segment, membership in its endpoint rectangle is
equivalent to membership in the closed segment. -/
theorem GridSegment.contains_of_axisAligned_of_in_coordinateRectangle
    {segment : GridSegment} {point : Cell}
    (aligned : segment.IsAxisAligned)
    (bounded :
      InClosedGridRectangle
        segment.coordinateLower segment.coordinateUpper point) :
    segment.Contains point := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  simp only [InClosedGridRectangle,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper] at bounded
  simp only [GridSegment.Contains,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.Between]
  rcases aligned with horizontal | vertical
  · left
    rcases horizontal with ⟨sameY, differentX⟩
    subst finishY
    exact ⟨⟨rfl, differentX⟩, by omega, by omega⟩
  · right
    rcases vertical with ⟨sameX, differentY⟩
    subst finishX
    exact ⟨⟨rfl, differentY⟩, by omega, by omega⟩

/-- A translated final occurrence suffix remains in the radius-96 rectangle
around its translated canonical literal center. -/
theorem retainedFinalTranslatedOccurrenceSuffix_point_in_centerRectangle
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell)
    {point : Cell}
    (pointMember :
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
      point ∈
        translatePolyline
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).translation relativeTranslate)
          suffix) :
    let target :=
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
    InClosedGridRectangle
      (coordinateRadiusLower 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          target))
      (coordinateRadiusUpper 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          target))
      point := by
  dsimp only at pointMember ⊢
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
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let suffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order scaledClause
        literal clauseIndex literalIndex)
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let target :=
    Cell.add
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
      sourceTranslate
  change point ∈ translatePolyline physicalTranslate suffix at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨originalPoint, originalPointMember, rfl⟩
  have originalBounded :=
    scaledAngularOccurrenceSuffix_point_in_centerRectangle
      placement order scaledClause literal clauseIndex literalIndex
      originalPointMember
  have originalCenterEq :
      Cell.scale
          (retainedTerminalFanRoutingRefinement *
            PeriodicEightOccurrenceSplitPositioned.refinementScale)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement scaledClause literal) =
        Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal) := by
    dsimp only [placement, scaledClause]
    rw [
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
      Cell.scale_scale]
    norm_num [retainedTerminalFanTotalRefinement_eq,
      retainedTerminalFanRoutingRefinement,
      retainedAngularFanSourceClearanceFactor,
      PeriodicEightOccurrenceSplitPositioned.refinementScale]
  rw [originalCenterEq] at originalBounded
  have translatedBounded :=
    InClosedGridRectangle.add originalBounded physicalTranslate
  have physicalEq :
      physicalTranslate =
        Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          sourceTranslate := by
    dsimp only [physicalTranslate, sourceTranslate]
    rw [retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
    simp [Cell.scale_scale]
  rw [physicalEq] at translatedBounded
  rw [physicalEq]
  change
    InClosedGridRectangle
      (coordinateRadiusLower 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          target))
      (coordinateRadiusUpper 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          target))
      (Cell.add
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          sourceTranslate)
        originalPoint)
  rcases centerEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal with
    ⟨centerX, centerY⟩
  rcases sourceTranslate with ⟨translateX, translateY⟩
  norm_num [target, centerEq, InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.add, Cell.scale] at translatedBounded ⊢
  omega

/-- If the translated suffix center lies outside a direct choice's source
segment rectangle, the direct source-to-boundary route strictly avoids that
suffix. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_centerOutside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice)
    (firstLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (firstClauseIndex firstLiteralIndex : Nat)
    (secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (secondClauseIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (centerOutside :
      let translatedCenter :=
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        translatedCenter) :
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
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        secondSuffix) := by
  dsimp only
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let translatedCenter :=
    Cell.add
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        secondClause secondLiteral)
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
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
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (secondClause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
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
        coordinateRadiusLower 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            translatedCenter))
      (secondUpper :=
        coordinateRadiusUpper 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            translatedCenter))
  · intro point pointMember
    simpa [firstSlot, retainedAngularFanSourceClearanceFactor] using
      choice.completeRoute_point_in_sourceSegmentRectangle
        firstSlot pointMember
  · intro point pointMember
    exact
      retainedFinalTranslatedOccurrenceSuffix_point_in_centerRectangle
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate
        (by simpa [source, placement, routes, secondSuffix] using pointMember)
  · exact
      retainedDirectSource_scaledSourceRectangle_separated_pointSpokeRectangle
        choice (by simpa [translatedCenter] using centerOutside)

/-- The translated canonical target center of another incidence lies outside
the source-segment rectangle of an axis-aligned successful direct choice. -/
theorem
    retainedFinalCoordinatedAlignedDirectSourceSegment_translatedCanonicalLiteralPosition_outsideRectangle_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = some choice)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    ¬InClosedGridRectangle
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)) := by
  have representedSegment :
      let route :=
        finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex
      (⟨polylineLastEntrance route, route.getLastD (0, 0)⟩ :
        GridSegment) = choice.sourceSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula firstClauseIndex firstLiteralIndex choice choiceLookup
  have representedSegment' :
      (⟨polylineLastEntrance
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex),
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex).getLastD (0, 0)⟩ :
        GridSegment) = choice.sourceSegment := by
    simpa only using representedSegment
  have sourceFinalAligned :
      let route :=
        finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    change
      (⟨polylineLastEntrance
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex),
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned
    rw [representedSegment']
    exact directAligned
  have sourceFinalAvoid :
      let route :=
        finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex
      let finalSegment : GridSegment :=
        ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
      let target :=
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
      finalSegment.IsAxisAligned ∧ ¬finalSegment.Contains target :=
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedCanonicalLiteralPosition_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember sourceFinalAligned
      relativeTranslate centersDifferent
  let translatedCenter :=
    Cell.add
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        secondClause secondLiteral)
      ((finalCoordinatedPlacement formula).translation
        relativeTranslate)
  intro bounded
  have contained :=
    LeanTrominoes.PeriodicOrthocrossing.GridSegment.contains_of_axisAligned_of_in_coordinateRectangle
      directAligned bounded
  rw [← representedSegment'] at contained
  exact sourceFinalAvoid.2 contained

/-- An axis-aligned successful direct source-to-boundary route strictly
avoids a translated occurrence suffix whenever their canonical centers are
different. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = some choice)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
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
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        secondSuffix) := by
  dsimp only
  apply
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_centerOutside
      formula choice firstLiteral firstClauseIndex firstLiteralIndex
      secondClause secondLiteral secondClauseIndex secondLiteralIndex
      relativeTranslate
  exact
    retainedFinalCoordinatedAlignedDirectSourceSegment_translatedCanonicalLiteralPosition_outsideRectangle_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember choiceLookup directAligned
      relativeTranslate centersDifferent

end PeriodicOrthocrossing
end LeanTrominoes
