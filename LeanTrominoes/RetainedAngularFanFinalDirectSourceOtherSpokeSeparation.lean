import LeanTrominoes.RetainedAngularFanDirectSourceOtherSpokeSeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseOccurrenceSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOtherSourceNeighborhood

/-!
# Final direct prefixes avoid other shared-center occurrence suffixes

The direct-source atlas proves that a coordinated prefix avoids every
different Figure 7 spoke at its own variable center.  This file identifies
that finite spoke with the actual positioned suffix of an incidence in
another final source clause.

At a shared canonical variable center, different source clauses select
different angular slots.  The finite atlas certificate therefore transports
directly to the final occurrence family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- After the final common refinement, a direct source route's radius-288
rectangle is separated from the radius-96 neighborhood of every lattice
point outside its original endpoint rectangle. -/
theorem
    retainedDirectSource_scaledSourceRectangle_separated_pointSpokeRectangle
    (choice : RetainedDirectSourceRouteChoice)
    {point : Cell}
    (outside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        point) :
    ClosedGridRectanglesSeparated
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      (coordinateRadiusLower 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point))
      (coordinateRadiusUpper 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point)) := by
  have separated :=
    ClosedGridRectanglesSeparated.scale_both_coordinateRadius
      (GridSegment.coordinateRectangle_separated_point_of_not_in
        (segment := choice.sourceSegment) outside)
      (factor := retainedTerminalFanTotalRefinement * 4)
      (radius := 288)
      (by native_decide)
      (by native_decide)
  norm_num [retainedTerminalFanTotalRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    retainedTerminalFanRoutingRefinement] at separated ⊢
  simp only [ClosedGridRectanglesSeparated,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at separated ⊢
  rcases separated with
      forwardX | backwardX | forwardY | backwardY
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- A successful direct occurrence's coordinated prefix strictly avoids
the Figure 7 suffix of an incidence in another clause at the same canonical
variable center. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_crossClauseOccurrenceSuffix_of_sameCenter
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
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
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
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      secondSuffix := by
  dsimp only
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
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let secondScaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      secondRawRoute
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  let secondBoundary :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset
          secondScaledClause secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex))
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCrossClauseCoordinatedOccurrenceSlots_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
  have localSeparated :
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot)
        (choice.figure7Spoke secondSlot) :=
    choice.completeRoute_strictlyAvoid_otherFigure7Spoke
      firstSlot secondSlot slotsDifferent
  have secondSlotVal :
      secondSlot.val =
        angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex := by
    simpa [source, routes, order, secondSlot,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have secondSuffixHead :
      secondSuffix.head? = some secondBoundary := by
    simp [secondSuffix, secondBoundary, scalePolyline]
  have secondScaledLast :
      secondScaledRoute.getLastD (0, 0) =
        Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral) := by
    have routeLast :
        secondScaledRoute.getLast? =
          some
            (Cell.scale retainedAngularFanSourceClearanceFactor
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (finalCoordinatedPlacement formula)
                secondClause secondLiteral)) := by
      simpa [secondScaledRoute, secondRawRoute] using
        finalCoordinatedScaledSourceRoute_getLast?
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondClauseMember secondLiteralMember
    simp [List.getLastD_eq_getLast?, routeLast]
  have boundaryPointEq :
      Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondScaledRoute.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) =
        secondBoundary := by
    simpa [source, placement, routes, order,
      secondRawRoute, secondScaledRoute,
      secondScaledClause, secondSlot, secondBoundary] using
      finalCoordinatedFallbackBoundaryPoint_eq_scaledOccurrenceBoundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have choiceCenter :
      Cell.add choice.origin
          ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0)) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral := by
    change
      choice.sourceSegment.finish =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral
    exact
      retainedFinalDirectSourceRouteChoice_sourceSegment_finish
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember firstLiteralMember choiceSome
  have choiceBoundary :
      (choice.completeRoute secondSlot).getLast? =
        some secondBoundary := by
    rw [
      choice.completeRoute_getLast_eq_scaledLocalLast,
      choiceCenter, centersEqual]
    apply congrArg some
    calc
      Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale 4
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (finalCoordinatedPlacement formula)
                secondClause secondLiteral)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) =
        Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondScaledRoute.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) := by
          rw [secondScaledLast]
          simp [retainedAngularFanSourceClearanceFactor]
      _ = secondBoundary := boundaryPointEq
  have spokeEq :
      choice.figure7Spoke secondSlot = secondSuffix := by
    exact
      choice.figure7Spoke_eq_scaledAngularOccurrenceSuffix
        placement order secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex
        secondSlot secondSlotVal
        (choiceBoundary.trans secondSuffixHead.symm)
  change
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot) secondSuffix
  rw [← spokeEq]
  exact localSeparated

/-- A successful direct occurrence's coordinated prefix strictly avoids
another occurrence's Figure 7 suffix whenever that occurrence's canonical
center lies outside the direct source segment's endpoint rectangle. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_occurrenceSuffix_of_centerOutside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice)
    {secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    {secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {secondLiteralIndex : Nat}
    (firstSlot : RetainedTerminalSlot)
    (centerOutside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)) :
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
      (choice.completeRoute firstSlot)
      secondSuffix := by
  dsimp only
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
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let secondCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      secondClause secondLiteral
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter))
      (secondUpper :=
        coordinateRadiusUpper 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter))
  · intro point pointMember
    exact choice.completeRoute_point_in_sourceSegmentRectangle
      firstSlot pointMember
  · intro point pointMember
    change point ∈ secondSuffix at pointMember
    have bounded :=
      scaledAngularOccurrenceSuffix_point_in_centerRectangle
        placement order secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex
        pointMember
    have suffixCenterEq :
        Cell.scale
            (retainedTerminalFanRoutingRefinement *
              PeriodicEightOccurrenceSplitPositioned.refinementScale)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement secondScaledClause secondLiteral) =
          Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter := by
      dsimp only [placement, secondScaledClause, secondCenter]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        Cell.scale_scale]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    rw [suffixCenterEq] at bounded
    exact bounded
  · exact
      retainedDirectSource_scaledSourceRectangle_separated_pointSpokeRectangle
        choice
        (by simpa [secondCenter] using centerOutside)

end PeriodicOrthocrossing
end LeanTrominoes
