import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherSpokeSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedBoundaryAssembly

/-!
# Mixed direct/fallback occurrence-route assembly

A final coordinated direct occurrence and a fallback occurrence are each an
endpoint join of a source-to-boundary prefix and the unchanged Figure 7
suffix.  This file packages the purely structural last step of their strict
separation: four strict piece-pair certificates assemble into strict
separation of the two complete occurrence routes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Four strict piece-pair certificates separate a complete coordinated
direct occurrence from any endpoint-joined fallback occurrence.  The
validated direct choice supplies its own prefix/suffix boundary equation. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (fallbackPrefix fallbackSuffix : List Cell)
    (fallbackBoundary : Cell)
    (fallbackPrefixLast :
      fallbackPrefix.getLast? = some fallbackBoundary)
    (fallbackSuffixHead :
      fallbackSuffix.head? = some fallbackBoundary)
    (prefixPrefixAvoid :
      let slot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute slot) fallbackPrefix)
    (prefixSuffixAvoid :
      let slot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute slot) fallbackSuffix)
    (suffixPrefixAvoid :
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
      RoutesStrictlyAvoidEachOther suffix fallbackPrefix)
    (suffixSuffixAvoid :
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
      RoutesStrictlyAvoidEachOther suffix fallbackSuffix) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (joinAtEndpoint fallbackPrefix fallbackSuffix) := by
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
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let suffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
  let directBoundary :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement literal.atom
        (incidenceRelativeOffset
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex))
  have directJoin :
      (choice.completeRoute slot).getLast? = suffix.head? := by
    simpa [finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes,
      source, placement, routes, slot, suffix] using
      retainedFinalCoordinatedDirectOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
  have suffixHead : suffix.head? = some directBoundary := by
    simp [suffix, directBoundary, scalePolyline]
  have prefixAvoidFallback :
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute slot)
        (joinAtEndpoint fallbackPrefix fallbackSuffix) :=
    prefixPrefixAvoid.join_right prefixSuffixAvoid
      fallbackPrefixLast fallbackSuffixHead
  have suffixAvoidFallback :
      RoutesStrictlyAvoidEachOther suffix
        (joinAtEndpoint fallbackPrefix fallbackSuffix) :=
    suffixPrefixAvoid.join_right suffixSuffixAvoid
      fallbackPrefixLast fallbackSuffixHead
  have joined :=
    prefixAvoidFallback.join_left suffixAvoidFallback
      (directJoin.trans suffixHead) suffixHead
  simpa [retainedFinalCoordinatedDirectOccurrenceRoute,
    source, placement, routes, slot, suffix] using joined

/-- For different genuine source clauses, existing Figure 7 geometry
automatically supplies both piece pairs involving the fallback suffix.
Thus complete mixed occurrence separation reduces exactly to the two
interactions between the direct occurrence pieces and the fallback boundary
prefix. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseJoin_of_prefix_pieces
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
          formula firstClauseIndex firstLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (fallbackPrefix : List Cell)
    (fallbackBoundary : Cell)
    (fallbackPrefixLast :
      fallbackPrefix.getLast? = some fallbackBoundary)
    (fallbackSuffixHead :
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
      secondSuffix.head? = some fallbackBoundary)
    (directPrefixAvoidFallbackPrefix :
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot) fallbackPrefix)
    (directSuffixAvoidFallbackPrefix :
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
      let firstSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (firstClause.scale retainedAngularFanSourceClearanceFactor)
            firstLiteral firstClauseIndex firstLiteralIndex)
      RoutesStrictlyAvoidEachOther firstSuffix fallbackPrefix) :
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
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (firstClause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral firstClauseIndex firstLiteralIndex)
      (joinAtEndpoint fallbackPrefix secondSuffix) := by
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
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (secondClause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  have directPrefixAvoidFallbackSuffix :
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot) secondSuffix := by
    simpa [source, placement, routes, secondSuffix] using
      retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_crossClauseOccurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceLookup clauseIndicesDifferent
  have suffixesAvoid :
      let firstSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (firstClause.scale retainedAngularFanSourceClearanceFactor)
            firstLiteral firstClauseIndex firstLiteralIndex)
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix := by
    simpa [source, placement, routes, secondSuffix] using
      retainedFinalCrossClauseOccurrenceSuffixes_strictlyAvoid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      firstClauseMember firstLiteralMember choiceLookup
      fallbackPrefix secondSuffix fallbackBoundary
      fallbackPrefixLast fallbackSuffixHead
      directPrefixAvoidFallbackPrefix directPrefixAvoidFallbackSuffix
      directSuffixAvoidFallbackPrefix suffixesAvoid

/-- A complete mixed cross-clause occurrence pair reduces to one geometric
premise: the coordinated direct prefix must avoid the boundary prefix
selected by the failed fallback lookup.  All joins and every Figure 7
suffix interaction are discharged here. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_prefix
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
          formula firstClauseIndex firstLiteralIndex =
        some choice)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (directPrefixAvoidFallbackPrefix :
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot)
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula secondLiteral
          secondClauseIndex secondLiteralIndex)) :
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
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (firstClause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral firstClauseIndex firstLiteralIndex)
      (joinAtEndpoint
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula secondLiteral
          secondClauseIndex secondLiteralIndex)
        secondSuffix) := by
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
  let fallbackPrefix :=
    retainedFinalCoordinatedFallbackBoundaryPrefix
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (secondClause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex)
  let fallbackBoundary :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex))
  have fallbackJoin :
      fallbackPrefix.getLast? = secondSuffix.head? := by
    simpa [source, placement, routes, order,
      fallbackPrefix, secondSuffix] using
      retainedFinalCoordinatedFallbackBoundaryPrefix_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have secondSuffixHead :
      secondSuffix.head? = some fallbackBoundary := by
    simp [secondSuffix, fallbackBoundary, scalePolyline]
  have fallbackPrefixLast :
      fallbackPrefix.getLast? = some fallbackBoundary :=
    fallbackJoin.trans secondSuffixHead
  have directSuffixAvoidFallbackPrefix :
      let firstSuffix :=
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement order
            (firstClause.scale retainedAngularFanSourceClearanceFactor)
            firstLiteral firstClauseIndex firstLiteralIndex)
      RoutesStrictlyAvoidEachOther firstSuffix fallbackPrefix := by
    have avoid :=
      retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_crossClauseOccurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember firstClauseMember
        secondLiteralMember firstLiteralMember
        secondChoiceNone (Ne.symm clauseIndicesDifferent)
    simpa [source, placement, routes, order,
      fallbackPrefix] using avoid.symm
  simpa [source, placement, routes, order,
    fallbackPrefix, secondSuffix] using
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseJoin_of_prefix_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      choiceLookup clauseIndicesDifferent
      fallbackPrefix fallbackBoundary
      fallbackPrefixLast secondSuffixHead
      directPrefixAvoidFallbackPrefix
      directSuffixAvoidFallbackPrefix

/-- Symmetric orientation of the mixed occurrence-route assembly theorem. -/
theorem
    join_strictlyAvoids_retainedFinalCoordinatedDirectOccurrenceRoute_of_pieces
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
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
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (fallbackPrefix fallbackSuffix : List Cell)
    (fallbackBoundary : Cell)
    (fallbackPrefixLast :
      fallbackPrefix.getLast? = some fallbackBoundary)
    (fallbackSuffixHead :
      fallbackSuffix.head? = some fallbackBoundary)
    (prefixPrefixAvoid :
      let slot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex
      RoutesStrictlyAvoidEachOther
        fallbackPrefix (choice.completeRoute slot))
    (prefixSuffixAvoid :
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
      RoutesStrictlyAvoidEachOther fallbackPrefix suffix)
    (suffixPrefixAvoid :
      let slot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex
      RoutesStrictlyAvoidEachOther
        fallbackSuffix (choice.completeRoute slot))
    (suffixSuffixAvoid :
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
      RoutesStrictlyAvoidEachOther fallbackSuffix suffix) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint fallbackPrefix fallbackSuffix)
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex) := by
  exact
    (retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember choiceLookup
      fallbackPrefix fallbackSuffix fallbackBoundary
      fallbackPrefixLast fallbackSuffixHead
      prefixPrefixAvoid.symm suffixPrefixAvoid.symm
      prefixSuffixAvoid.symm suffixSuffixAvoid.symm).symm

end PeriodicOrthocrossing
end LeanTrominoes
