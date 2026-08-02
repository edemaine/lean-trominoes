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

set_option maxHeartbeats 8000000

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
  change
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        firstRoute firstTerminal firstSlot)
      secondSuffix
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

/-- The ordinary fallback boundary splice of one final incidence strictly
avoids the Figure 7 suffix of an incidence at a different canonical variable
center.  Retained source planarity supplies clearance from the other raw
route endpoint, and source scaling expands it past the bounded suffix. -/
theorem
    retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix_of_distinctCenters
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
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
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
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
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let rawSource := finalCoordinatedSource formula
  let rawPlacement := finalCoordinatedPlacement formula
  let rawRoutes := finalCoordinatedSourceRoutes formula
  let source :=
    rawSource.scale retainedAngularFanSourceClearanceFactor
  let placement :=
    rawPlacement.scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor rawRoutes
  let order := angularOccurrenceOrder source.erase routes
  let firstRawRoute :=
    rawRoutes firstClauseIndex firstLiteralIndex
  let secondRawRoute :=
    rawRoutes secondClauseIndex secondLiteralIndex
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRawRoute
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      firstRawTerminal
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral
      firstClauseIndex firstLiteralIndex
  let target :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      rawPlacement secondClause secondLiteral
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (secondClause.scale
          retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  change
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        firstRoute firstTerminal firstSlot)
      secondSuffix
  have copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        rawSource rawPlacement rawRoutes
        firstClauseMember firstLiteralMember with
    ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        rawSource rawPlacement rawRoutes
        secondClauseMember secondLiteralMember with
    ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
  have routeIndicesDifferent :
      firstRouteIndex ≠ secondRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember
        indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    simpa using
      congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
  have firstLength : 2 ≤ firstRawRoute.length := by
    simpa [firstRawRoute, rawRoutes, rawSource] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRawRoute.length := by
    simpa [secondRawRoute, rawRoutes, rawSource] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      secondClauseMember secondLiteralMember
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have firstHeadNeSecondLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      rawSource rawPlacement rawRoutes compatible
      _ _
      firstIncidenceMember secondIncidenceMember
  have firstSourceNeTarget :
      PositionedPeriodicCNF.canonicalClausePosition
          rawPlacement firstClause ≠
        target := by
    rw [firstEndpoints.1, secondEndpoints.2]
      at firstHeadNeSecondLast
    simpa [target, firstRawRoute, secondRawRoute,
      rawRoutes] using firstHeadNeSecondLast
  have prefixClearance :
      (∀ point ∈ firstRawRoute.dropLast,
          point ≠ target) ∧
        ∀ segment ∈ gridPolylineSegments firstRawRoute.dropLast,
          segment.IsAxisAligned →
            ¬segment.Contains target := by
    exact
      retainedDeduplicatedGaugedWrappedDrawing_routePrefix_avoids_otherFinal
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent
        (by simpa [firstRawRoute, rawRoutes, rawPlacement] using
          firstEndpoints.1)
        (by simpa [secondRawRoute, rawRoutes, rawPlacement, target] using
          secondEndpoints.2)
        firstSourceNeTarget
  let firstFinalSegment : GridSegment :=
    ⟨polylineLastEntrance firstRawRoute,
      firstRawRoute.getLastD (0, 0)⟩
  have firstFinalAligned :
      firstFinalSegment.IsAxisAligned := by
    simpa [firstFinalSegment, firstRawRoute, rawRoutes] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
  have sourceAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
      firstRouteMember secondRouteMember
      firstLength secondLength routeIndicesDifferent
  have firstFinalMember :
      firstFinalSegment ∈
        gridPolylineSegments firstRawRoute := by
    simpa [firstFinalSegment, firstRawRoute, rawRoutes] using
      finalCoordinatedSourceRoute_finalSegment_mem
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have targetMember : target ∈ secondRawRoute := by
    exact mem_of_getLast?_eq_some
      (by simpa [secondRawRoute, rawRoutes, rawPlacement, target] using
        secondEndpoints.2)
  have firstFinalAvoidsInterior :
      ¬firstFinalSegment.InteriorContains target :=
    sourceAvoid.secondPointsAvoid_of_mem
      target targetMember firstFinalSegment firstFinalMember
  have reverseTailExists :
      ∃ entrance, firstRawRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      firstRawRoute firstLength
  have entranceLast :
      firstRawRoute.dropLast.getLast? =
        some (polylineLastEntrance firstRawRoute) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have firstEntranceNeTarget :
      polylineLastEntrance firstRawRoute ≠ target :=
    prefixClearance.1
      (polylineLastEntrance firstRawRoute)
      (mem_of_getLast?_eq_some entranceLast)
  have firstLastD :
      firstRawRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          rawPlacement firstClause firstLiteral := by
    rw [List.getLastD_eq_getLast?]
    change
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).getLast?.getD
          (0, 0) = _
    rw [firstEndpoints.2]
    rfl
  have firstFinishNeTarget :
      firstRawRoute.getLastD (0, 0) ≠ target := by
    rw [firstLastD]
    simpa [rawPlacement, target] using centersDifferent
  have firstFinalAvoidsTarget :
      ¬firstFinalSegment.Contains target := by
    intro contains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          contains with
      interior | endpoint
    · exact firstFinalAvoidsInterior interior
    · rcases endpoint with atStart | atFinish
      · exact firstEntranceNeTarget
          (by simpa [firstFinalSegment] using atStart.symm)
      · exact firstFinishNeTarget
          (by simpa [firstFinalSegment] using atFinish.symm)
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRawRoute) =
        some firstRawTerminal := by
    simpa [firstRawRoute, firstRawTerminal, rawRoutes] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember
  have secondSuffixBounded :
      ∀ point ∈ secondSuffix,
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
          Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            target := by
      dsimp only [placement, rawPlacement, target]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        Cell.scale_scale]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    rw [suffixCenterEq] at bounded
    exact bounded
  have separated :=
    retainedAngularFanSourceScaledSplicedBoundaryPolyline_strictlyAvoids_pointNeighborhood
      retainedAngularFanSourceClearanceFactor_pos
      (by native_decide)
      firstRawRoute firstRawTerminal firstSlot
      firstLength firstClassified target
      prefixClearance.1 prefixClearance.2
      firstFinalAligned firstFinalAvoidsTarget
      secondSuffix secondSuffixBounded
  simpa only [firstRoute, firstTerminal] using separated

/-- The ordinary fallback boundary splice of one genuine final incidence
strictly avoids the Figure 7 suffix of every incidence in a different
clause, whether or not the two canonical variable centers coincide. -/
theorem
    retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
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
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · exact
      retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
  · exact
      retainedFinalCrossClauseOrdinaryBoundarySplice_strictlyAvoid_occurrenceSuffix_of_distinctCenters
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone clauseIndicesDifferent centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
