import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOccurrenceSeparation

/-!
# Completed cross-clause separation for final fallbacks

For ordinary failed-selector routes in different final source clauses, the
boundary splices, the two directed boundary/suffix pairings, and the two
Figure 7 suffixes are all strictly separated.  This file joins those four
certificates at the fan boundary and transports the result to the public
coordinated route family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- The complete ordinary fallback occurrence routes of two genuine entries
in different final source clauses are contact-free. -/
theorem
    retainedFinalCrossClauseOrdinaryFallbackExplicitOccurrenceRoutes_strictlyAvoid
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
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
    let firstScaledClause :=
      firstClause.scale retainedAngularFanSourceClearanceFactor
    let secondScaledClause :=
      secondClause.scale retainedAngularFanSourceClearanceFactor
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let secondRawRoute :=
      finalCoordinatedSourceRoutes
        formula secondClauseIndex secondLiteralIndex
    let firstRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector firstRawRoute)
    let secondRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector secondRawRoute)
    let firstRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        firstRawRoute
    let secondRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        secondRawRoute
    let firstTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor firstRawTerminal
    let secondTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor secondRawTerminal
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    let firstPrefix :=
      retainedAngularFanSplicedBoundaryRoute
        firstRoute firstTerminal firstSlot
    let secondPrefix :=
      retainedAngularFanSplicedBoundaryRoute
        secondRoute secondTerminal secondSlot
    let firstSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          firstScaledClause firstLiteral
          firstClauseIndex firstLiteralIndex)
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          secondScaledClause secondLiteral
          secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint firstPrefix firstSuffix)
      (joinAtEndpoint secondPrefix secondSuffix) := by
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
  let firstScaledClause :=
    firstClause.scale retainedAngularFanSourceClearanceFactor
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let secondRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRawRoute)
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRawRoute
  let secondRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      secondRawRoute
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstRawTerminal
  let secondTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor secondRawTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      firstRoute firstTerminal firstSlot
  let secondPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      secondRoute secondTerminal secondSlot
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        firstScaledClause firstLiteral
        firstClauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  let firstMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset firstScaledClause firstLiteral)
        (angularOccurrenceIndex order
          firstLiteral firstClauseIndex firstLiteralIndex))
  let secondMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset secondScaledClause secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex))
  have firstLength :
      2 ≤ firstRawRoute.length := by
    exact
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength :
      2 ≤ secondRawRoute.length := by
    exact
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstRouteLength :
      2 ≤ firstRoute.length := by
    simpa [firstRoute, scalePolyline] using firstLength
  have secondRouteLength :
      2 ≤ secondRoute.length := by
    simpa [secondRoute, scalePolyline] using secondLength
  have firstRouteClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondRouteClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some secondTerminal := by
    simpa [secondRoute, secondTerminal,
      secondRawRoute, secondRawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstRawOrthogonal :
      OrthogonalPolyline firstRawRoute := by
    simpa [firstRawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
  have secondRawOrthogonal :
      OrthogonalPolyline secondRawRoute := by
    simpa [secondRawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember secondChoiceNone
  have firstSpliceOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      firstRoute firstTerminal firstSlot
      firstRouteLength firstRouteClassified
      (by
        simpa [firstRoute] using
          firstRawOrthogonal.scalePolyline
            retainedAngularFanSourceClearanceFactor_pos)
  have secondSpliceOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      secondRoute secondTerminal secondSlot
      secondRouteLength secondRouteClassified
      (by
        simpa [secondRoute] using
          secondRawOrthogonal.scalePolyline
            retainedAngularFanSourceClearanceFactor_pos)
  have prefixesAvoidPolyline :=
    retainedFinalCrossClauseFallbackOrdinaryBoundarySplices_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone clauseIndicesDifferent
  have firstPrefixAvoidsSecondSuffixPolyline :=
    retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone clauseIndicesDifferent
  have firstSuffixAvoidsSecondPrefixPolyline :=
    (retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      secondClauseMember firstClauseMember
      secondLiteralMember firstLiteralMember
      secondChoiceNone (Ne.symm clauseIndicesDifferent)).symm
  have suffixesAvoid :=
    retainedFinalCrossClauseOccurrenceSuffixes_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember clauseIndicesDifferent
  have firstPrefixEq :
      firstPrefix =
        retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot := by
    simpa [firstPrefix,
      retainedAngularFanSplicedBoundaryRoute] using
      rasterizeRetainedPolyline_eq_of_orthogonal
        firstSpliceOrthogonal
  have secondPrefixEq :
      secondPrefix =
        retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot := by
    simpa [secondPrefix,
      retainedAngularFanSplicedBoundaryRoute] using
      rasterizeRetainedPolyline_eq_of_orthogonal
        secondSpliceOrthogonal
  have prefixesAvoid :
      RoutesStrictlyAvoidEachOther firstPrefix secondPrefix := by
    rw [firstPrefixEq, secondPrefixEq]
    simpa [
      firstRoute, secondRoute, firstTerminal, secondTerminal,
      firstRawRoute, secondRawRoute,
      firstRawTerminal, secondRawTerminal,
      firstSlot, secondSlot] using prefixesAvoidPolyline.1
  have firstPrefixAvoidsSecondSuffix :
      RoutesStrictlyAvoidEachOther firstPrefix secondSuffix := by
    rw [firstPrefixEq]
    simpa [
      source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      firstRoute, firstTerminal,
      firstRawRoute, firstRawTerminal, firstSlot,
      secondSuffix] using firstPrefixAvoidsSecondSuffixPolyline
  have firstSuffixAvoidsSecondPrefix :
      RoutesStrictlyAvoidEachOther firstSuffix secondPrefix := by
    rw [secondPrefixEq]
    simpa [
      source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      secondRoute, secondTerminal,
      secondRawRoute, secondRawTerminal, secondSlot,
      firstSuffix] using firstSuffixAvoidsSecondPrefixPolyline
  have suffixesAvoid' :
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix := by
    simpa [source, placement, routes, order,
      firstScaledClause, secondScaledClause,
      firstSuffix, secondSuffix] using suffixesAvoid
  have firstEscapedValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapedValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstOrdinaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      firstRoute firstTerminal firstSlot
      firstRouteLength firstRouteClassified
      (by
        simpa [firstRoute, firstRawRoute] using
          finalCoordinatedScaledSourceRoute_retainedRay
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            firstClauseMember firstLiteralMember)
      (by
        simpa [firstRoute, firstRawRoute] using
          finalCoordinatedScaledSourceRoute_head
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            firstClauseMember firstLiteralMember)
  have secondOrdinaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      secondRoute secondTerminal secondSlot
      secondRouteLength secondRouteClassified
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_retainedRay
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            secondClauseMember secondLiteralMember)
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_head
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            secondClauseMember secondLiteralMember)
  have firstEscapedBoundary :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        firstRoute firstTerminal firstSlot).getLast? =
          firstSuffix.head? := by
    simpa [source, placement, routes, order,
      firstScaledClause, firstRawRoute, firstRawTerminal,
      firstSlot, firstRoute, firstTerminal, firstSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapedBoundary :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        secondRoute secondTerminal secondSlot).getLast? =
          secondSuffix.head? := by
    simpa [source, placement, routes, order,
      secondScaledClause, secondRawRoute, secondRawTerminal,
      secondSlot, secondRoute, secondTerminal, secondSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstBoundary :
      firstPrefix.getLast? = firstSuffix.head? := by
    calc
      firstPrefix.getLast? =
          (retainedAngularFanEscapedSplicedBoundaryRoute
            firstRoute firstTerminal firstSlot).getLast? := by
        exact
          firstOrdinaryValid.2.1.trans
            (by
              simpa [firstRawRoute, firstRawTerminal,
                firstSlot, firstRoute, firstTerminal] using
                firstEscapedValid.2.1.symm)
      _ = firstSuffix.head? := firstEscapedBoundary
  have secondBoundary :
      secondPrefix.getLast? = secondSuffix.head? := by
    calc
      secondPrefix.getLast? =
          (retainedAngularFanEscapedSplicedBoundaryRoute
            secondRoute secondTerminal secondSlot).getLast? := by
        exact
          secondOrdinaryValid.2.1.trans
            (by
              simpa [secondRawRoute, secondRawTerminal,
                secondSlot, secondRoute, secondTerminal] using
                secondEscapedValid.2.1.symm)
      _ = secondSuffix.head? := secondEscapedBoundary
  have firstSuffixHead :
      firstSuffix.head? = some firstMiddle := by
    simp [firstSuffix, firstMiddle, scalePolyline]
  have secondSuffixHead :
      secondSuffix.head? = some secondMiddle := by
    simp [secondSuffix, secondMiddle, scalePolyline]
  have firstPrefixAvoidsSecondComplete :=
    prefixesAvoid.join_right
      firstPrefixAvoidsSecondSuffix
      (secondBoundary.trans secondSuffixHead)
      secondSuffixHead
  have firstSuffixAvoidsSecondComplete :=
    firstSuffixAvoidsSecondPrefix.join_right
      suffixesAvoid'
      (secondBoundary.trans secondSuffixHead)
      secondSuffixHead
  exact
    firstPrefixAvoidsSecondComplete.join_left
      firstSuffixAvoidsSecondComplete
      (firstBoundary.trans firstSuffixHead)
      firstSuffixHead

/-- In the non-singleton failed-selector branch, different genuine clauses of
the public coordinated route family are strictly separated. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_choices_none_of_prefix_lengths_ne_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (firstPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast.length ≠ 1)
    (secondPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula secondClauseIndex secondLiteralIndex).dropLast.length ≠ 1)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
      formula firstClauseIndex firstLiteralIndex
      firstChoiceNone firstPrefixLengthNeOne,
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
      formula secondClauseIndex secondLiteralIndex
      secondChoiceNone secondPrefixLengthNeOne,
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember]
  exact
    retainedFinalCrossClauseOrdinaryFallbackExplicitOccurrenceRoutes_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone clauseIndicesDifferent

end PeriodicOrthocrossing
end LeanTrominoes
