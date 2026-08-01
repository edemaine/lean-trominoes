import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanSourceSplicePointSeparation

/-!
# Cross-clause fallback boundaries avoid occurrence suffixes

At a shared variable center, route simplicity clears the refined copied
source prefix from the radius-96 Figure 7 neighborhood.  The positioned
outer-fan atlas clears the replacement route from every different occurrence
spoke.  This file joins those two facts for genuine final incidences.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- The ordinary fallback boundary splice of one final incidence strictly
avoids the Figure 7 suffix of an incidence in a different clause when the
two incidences share their canonical variable center. -/
theorem
    retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
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
    let order := angularOccurrenceOrder source.erase routes
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let firstRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        firstRawRoute
    let firstTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (classifiedRetainedTerminalData
          (routeTerminalVector firstRawRoute))
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral
        firstClauseIndex firstLiteralIndex
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (secondClause.scale
            retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        firstRoute firstTerminal firstSlot)
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
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRawRoute
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      firstRawTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral
      firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral
      secondClauseIndex secondLiteralIndex
  let firstFinalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        firstClause firstLiteral)
  let secondFinalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        secondClause secondLiteral)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      firstFinalPoint
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (secondClause.scale
          retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  have finalPointsEqual :
      firstFinalPoint = secondFinalPoint := by
    exact congrArg
      (Cell.scale retainedAngularFanSourceClearanceFactor)
      centersEqual
  have refinedCentersEqual :
      Cell.scale retainedTerminalFanTotalRefinement
          firstFinalPoint =
        Cell.scale retainedTerminalFanTotalRefinement
          secondFinalPoint :=
    congrArg
      (Cell.scale retainedTerminalFanTotalRefinement)
      finalPointsEqual
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCrossClauseCoordinatedOccurrenceSlots_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
  have routeLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have simple :
      LocalIncidenceDrawing.RouteIsSimple firstRoute := by
    simpa [firstRoute, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have routeFinal :
      firstRoute.getLast? = some firstFinalPoint := by
    simpa [firstRoute, firstRawRoute, firstFinalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have terminalLengthPositive : 0 < firstTerminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength firstTerminal := by
    simpa [firstTerminal, firstRawTerminal, firstRawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal := by
    have escapePositive :
        0 < retainedTerminalFanOuterSourceEscapeLength := by
      native_decide
    omega
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt
          center secondSlot =
        secondSuffix := by
    rw [show center =
        Cell.scale retainedTerminalFanTotalRefinement
          secondFinalPoint by
      exact refinedCentersEqual]
    simpa [source, placement, routes, order,
      secondFinalPoint, secondSlot, secondSuffix] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have replacementAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          center firstTerminal firstSlot)
        secondSuffix := by
    rw [← spokeEqual]
    exact
      retainedTerminalFanOuterCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
        center firstTerminal firstSlot secondSlot
        terminalLengthPositive radialLengthPositive slotsDifferent
  have secondSuffixBounded :
      ∀ point ∈ secondSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96 center)
          (coordinateRadiusUpper 96 center)
          point := by
    intro point pointMember
    have bounded :=
      scaledAngularOccurrenceSuffix_point_in_centerRectangle
        placement order
        (secondClause.scale
          retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex
        (by simpa [secondSuffix] using pointMember)
    have suffixCenterEq :
        Cell.scale
            (retainedTerminalFanRoutingRefinement *
              PeriodicEightOccurrenceSplitPositioned.refinementScale)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement
              (secondClause.scale
                retainedAngularFanSourceClearanceFactor)
              secondLiteral) =
          center := by
      dsimp only [placement, center, secondFinalPoint,
        firstFinalPoint]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        Cell.scale_scale, Cell.scale_scale]
      simpa [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
        using congrArg
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor))
          centersEqual.symm
    rw [suffixCenterEq] at bounded
    exact bounded
  simpa [source, placement, routes, order,
    firstRawRoute, firstRawTerminal,
    firstRoute, firstTerminal, firstSlot,
    firstFinalPoint, secondSuffix, center] using
    retainedAngularFanSplicedBoundaryPolyline_strictlyAvoids_ownPointNeighborhood_of_replacement
      firstRoute firstTerminal firstSlot firstFinalPoint
      secondSuffix routeLength classified simple routeFinal
      (by simpa [center] using secondSuffixBounded)
      (by simpa [center] using replacementAvoid)

end PeriodicOrthocrossing
end LeanTrominoes
