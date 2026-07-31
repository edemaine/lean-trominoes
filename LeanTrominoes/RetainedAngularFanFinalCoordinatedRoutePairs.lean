import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoicePairs
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Pairwise assembly for final coordinated occurrence routes

A specialized direct route joins its coordinated source-to-boundary prefix
to the unchanged scaled Figure 7 spoke.  Pairwise separation of the prefixes
is now unconditional for distinct literal indices of one final clause.

This module applies the generic endpoint-join separator and reduces
separation of the two actual occurrence routes to the three geometric pairs
that involve a Figure 7 suffix: the two directed prefix--suffix pairs and
the suffix--suffix pair.  The validated boundary equations discharge both
join conditions automatically.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Two successful coordinated occurrences of one final clause inherit
head-only pairwise separation once every suffix-involving piece pair is
strictly separated. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoutes_separated_of_suffix_pieces
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choiceFirst choiceSecond : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (choiceFirstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some choiceFirst)
    (choiceSecondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some choiceSecond)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstPrefixAvoidSecondSuffix :
      let source :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor
      let placement :=
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).scale retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral clauseIndex firstLiteralIndex
      let secondSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            secondLiteral clauseIndex secondLiteralIndex)
      RoutesStrictlyAvoidEachOther
        (choiceFirst.completeRoute firstSlot) secondSuffix)
    (firstSuffixAvoidSecondPrefix :
      let source :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor
      let placement :=
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).scale retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
      let secondSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral clauseIndex secondLiteralIndex
      let firstSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            firstLiteral clauseIndex firstLiteralIndex)
      RoutesStrictlyAvoidEachOther
        firstSuffix (choiceSecond.completeRoute secondSlot))
    (suffixesAvoid :
      let source :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor
      let placement :=
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).scale retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
      let firstSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            firstLiteral clauseIndex firstLiteralIndex)
      let secondSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            secondLiteral clauseIndex secondLiteralIndex)
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix) :
    RoutesAvoidEachOther
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceFirst
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceSecond
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex) ∧
      RoutesMeetOnlyAtHeads
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceFirst
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceSecond
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex) := by
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale retainedAngularFanSourceClearanceFactor
  let placement :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral clauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral clauseIndex secondLiteralIndex
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral clauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral clauseIndex secondLiteralIndex)
  let firstMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (OccurrenceSplitRing.angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          firstLiteral clauseIndex firstLiteralIndex))
  let secondMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (OccurrenceSplitRing.angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          secondLiteral clauseIndex secondLiteralIndex))
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have prefixesSeparated :=
    retainedFinalDirectSourceRouteChoices_completeRoutes_separated
      formula sourceCertificate.graphDegreeAtMostThree
      clauseIndex firstLiteralIndex secondLiteralIndex
      choiceFirst choiceSecond
      choiceFirstLookup choiceSecondLookup
      literalIndicesDifferent firstSlot secondSlot
  have firstBoundary :
      (choiceFirst.completeRoute firstSlot).getLast? =
        firstSuffix.head? := by
    simpa [source, placement, routes, firstSlot, firstSuffix] using
      retainedFinalCoordinatedDirectOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choiceFirst
        clauseMember firstLiteralMember choiceFirstLookup
  have secondBoundary :
      (choiceSecond.completeRoute secondSlot).getLast? =
        secondSuffix.head? := by
    simpa [source, placement, routes, secondSlot, secondSuffix] using
      retainedFinalCoordinatedDirectOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choiceSecond
        clauseMember secondLiteralMember choiceSecondLookup
  have firstSuffixHead :
      firstSuffix.head? = some firstMiddle := by
    simp [firstSuffix, firstMiddle, scalePolyline]
  have secondSuffixHead :
      secondSuffix.head? = some secondMiddle := by
    simp [secondSuffix, secondMiddle, scalePolyline]
  have joined :=
    prefixesSeparated.1.join_tails_of_prefixes_meet_only_at_heads
      prefixesSeparated.2
      (by simpa [source, placement, routes, firstSlot,
        secondSuffix] using firstPrefixAvoidSecondSuffix)
      (by simpa [source, placement, routes, secondSlot,
        firstSuffix] using firstSuffixAvoidSecondPrefix)
      (by simpa [source, placement, routes,
        firstSuffix, secondSuffix] using suffixesAvoid)
      (firstBoundary.trans firstSuffixHead) firstSuffixHead
      (secondBoundary.trans secondSuffixHead) secondSuffixHead
  simpa [retainedFinalCoordinatedDirectOccurrenceRoute,
    finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes,
    source, placement, routes, firstSlot, secondSlot,
    firstSuffix, secondSuffix] using joined

end PeriodicOrthocrossing
end LeanTrominoes
