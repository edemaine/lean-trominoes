import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

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
