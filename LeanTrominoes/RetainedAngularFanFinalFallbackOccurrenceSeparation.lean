import LeanTrominoes.RetainedAngularFanFinalFallbackSpliceSeparation
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutePairs

/-!
# Completed occurrence separation for an escaped final fallback

The exceptional singleton carrier fallback is now joined to its unchanged
Figure 7 suffix.  The boundary-prefix certificate, both directed
prefix/suffix certificates, and the existing suffix/suffix certificate feed
the generic endpoint-join theorem.  The ordinary completed route is then
identified with the established source-scaled occurrence route family.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- A delayed-lane singleton fallback and the established completed route
at every other literal of the same final source clause remain separated,
with their common clause head as their only possible contact. -/
theorem
    retainedFinalSameClauseEscapedFallbackExplicitOccurrenceRoutes_separated
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
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstSingletonPrefix :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length = 1) :
    RoutesAvoidEachOther
        (retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (joinAtEndpoint
          (retainedAngularFanSplicedBoundaryRoute
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes
                formula clauseIndex secondLiteralIndex))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (classifiedRetainedTerminalData
                (routeTerminalVector
                  (finalCoordinatedSourceRoutes
                    formula clauseIndex secondLiteralIndex))))
            (retainedFinalCoordinatedOccurrenceSlot
              formula secondLiteral clauseIndex secondLiteralIndex))
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix
              ((finalCoordinatedPlacement formula).scale
                retainedAngularFanSourceClearanceFactor)
              (angularOccurrenceOrder
                ((finalCoordinatedSource formula).scale
                  retainedAngularFanSourceClearanceFactor).erase
                (PositionedPeriodicCNF.scaleIncidenceRoutes
                  retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes formula)))
              (clause.scale retainedAngularFanSourceClearanceFactor)
              secondLiteral clauseIndex secondLiteralIndex))) ∧
      RoutesMeetOnlyAtHeads
        (retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (joinAtEndpoint
          (retainedAngularFanSplicedBoundaryRoute
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes
                formula clauseIndex secondLiteralIndex))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (classifiedRetainedTerminalData
                (routeTerminalVector
                  (finalCoordinatedSourceRoutes
                    formula clauseIndex secondLiteralIndex))))
            (retainedFinalCoordinatedOccurrenceSlot
              formula secondLiteral clauseIndex secondLiteralIndex))
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix
              ((finalCoordinatedPlacement formula).scale
                retainedAngularFanSourceClearanceFactor)
              (angularOccurrenceOrder
                ((finalCoordinatedSource formula).scale
                  retainedAngularFanSourceClearanceFactor).erase
                (PositionedPeriodicCNF.scaleIncidenceRoutes
                  retainedAngularFanSourceClearanceFactor
                  (finalCoordinatedSourceRoutes formula)))
              (clause.scale retainedAngularFanSourceClearanceFactor)
              secondLiteral clauseIndex secondLiteralIndex))) := by
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
  let order :=
    angularOccurrenceOrder source.erase routes
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex firstLiteralIndex
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex secondLiteralIndex
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let secondRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRawRoute)
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral clauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral clauseIndex secondLiteralIndex
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
  let firstPrefix :=
    retainedAngularFanEscapedSplicedBoundaryRoute
      firstRoute firstTerminal firstSlot
  let secondPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      secondRoute secondTerminal secondSlot
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        scaledClause firstLiteral clauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        scaledClause secondLiteral clauseIndex secondLiteralIndex)
  let firstMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset scaledClause firstLiteral)
        (angularOccurrenceIndex order
          firstLiteral clauseIndex firstLiteralIndex))
  let secondMiddle :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset scaledClause secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral clauseIndex secondLiteralIndex))
  have prefixPieces :=
    retainedFinalSameClauseEscapedOrdinarySplicedBoundaryRoutes_separated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember indicesDifferent
      firstChoiceNone firstSingletonPrefix
  have suffixesAvoid :
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix := by
    simpa [source, placement, routes, order,
      scaledClause, firstSuffix, secondSuffix,
      finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSuffixes_strictlyAvoid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember indicesDifferent
  have firstBoundary :
      firstPrefix.getLast? = firstSuffix.head? := by
    simpa [source, placement, routes, order,
      scaledClause, firstRawRoute, firstRawTerminal,
      firstSlot, firstRoute, firstTerminal,
      firstPrefix, firstSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember firstLiteralMember
  have secondEscapedValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember secondLiteralMember
  have secondOrdinaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      secondRoute secondTerminal secondSlot
      (by
        simpa [secondRoute, scalePolyline] using
          finalCoordinatedSourceRoutes_length_ge_two
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember secondLiteralMember)
      (by
        simpa [secondRoute, secondTerminal,
          secondRawRoute, secondRawTerminal] using
          finalCoordinatedScaledSourceRoute_classified
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember secondLiteralMember)
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_retainedRay
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember secondLiteralMember)
      (by
        simpa [secondRoute, secondRawRoute] using
          finalCoordinatedScaledSourceRoute_head
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember secondLiteralMember)
  have secondEscapedBoundary :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        secondRoute secondTerminal secondSlot).getLast? =
          secondSuffix.head? := by
    simpa [source, placement, routes, order,
      scaledClause, secondRawRoute, secondRawTerminal,
      secondSlot, secondRoute, secondTerminal,
      secondSuffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember secondLiteralMember
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
  have joined :=
    prefixPieces.1.join_tails_of_prefixes_meet_only_at_heads
      prefixPieces.2.1
      prefixPieces.2.2.1
      prefixPieces.2.2.2
      suffixesAvoid
      (firstBoundary.trans firstSuffixHead) firstSuffixHead
      (secondBoundary.trans secondSuffixHead) secondSuffixHead
  change
    RoutesAvoidEachOther
        (joinAtEndpoint firstPrefix firstSuffix)
        (joinAtEndpoint secondPrefix secondSuffix) ∧
      RoutesMeetOnlyAtHeads
        (joinAtEndpoint firstPrefix firstSuffix)
        (joinAtEndpoint secondPrefix secondSuffix)
  exact joined

/-- A genuine copied-source entry of the established final route family is
the corresponding explicit source/fan occurrence splice. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_splicedOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
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
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedAngularFanSplicedOccurrenceRoute
        source placement routes
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex := by
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
  let order :=
    angularOccurrenceOrder source.erase routes
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  have scaledClauseMember :
      (scaledClause, clauseIndex) ∈ source.clauses.zipIdx := by
    rw [show source =
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor by rfl]
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have scaledLiteralMember :
      (literal, literalIndex) ∈
        scaledClause.literals.zipIdx := by
    simpa [scaledClause] using literalMember
  have occurrenceIndex :
      clauseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx scaledClauseMember
    simpa [PeriodicEightOccurrenceSplitPositioned.occurrenceClauses]
      using indexLt
  change
    retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex =
      _
  rw [retainedAngularFanSplicedIncidenceRoutes_occurrence
    source placement routes clauseIndex literalIndex occurrenceIndex]
  exact
    retainedAngularFanSplicedOccurrenceRoutes_of_members
      source placement routes scaledClauseMember scaledLiteralMember

/-- Unfold a genuine spliced occurrence route into its boundary prefix and
unchanged Figure 7 suffix. -/
theorem splicedOccurrenceRoute_eq_explicitJoin
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedAngularFanSplicedOccurrenceRoute
        source placement routes clause literal
        clauseIndex literalIndex =
      joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (routes clauseIndex literalIndex)
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (routes clauseIndex literalIndex)))
          (boundedRetainedTerminalSlot
            (angularOccurrenceIndex
              (angularOccurrenceOrder source.erase routes)
              literal clauseIndex literalIndex)))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            clause literal clauseIndex literalIndex)) := by
  rw [retainedAngularFanSplicedOccurrenceRoute]
  rw [retainedAngularFanBoundaryIncidenceRoutes_of_members
    source routes clauseMember literalMember]

/-- At a genuine final copied-source incidence, the established route is
the explicit ordinary boundary splice joined to its Figure 7 suffix. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (classifiedRetainedTerminalData
              (routeTerminalVector
                (finalCoordinatedSourceRoutes
                  formula clauseIndex literalIndex))))
          (retainedFinalCoordinatedOccurrenceSlot
            formula literal clauseIndex literalIndex))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            (angularOccurrenceOrder
              ((finalCoordinatedSource formula).scale
                retainedAngularFanSourceClearanceFactor).erase
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes formula)))
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)) := by
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
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  have scaledClauseMember :
      (scaledClause, clauseIndex) ∈ source.clauses.zipIdx := by
    rw [show source =
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor by rfl]
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have scaledLiteralMember :
      (literal, literalIndex) ∈
        scaledClause.literals.zipIdx := by
    simpa [scaledClause] using literalMember
  rw [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_splicedOccurrenceRoute
      formula clauseMember literalMember,
    splicedOccurrenceRoute_eq_explicitJoin
      source placement routes scaledClauseMember scaledLiteralMember]
  have classified :=
    finalCoordinatedSourceRoute_classified
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have classified' :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex)) =
        some
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula clauseIndex literalIndex))) := by
    simpa using classified
  have terminalDataScale :
      classifiedRetainedTerminalData
          (routeTerminalVector
            (routes clauseIndex literalIndex)) =
        scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula clauseIndex literalIndex))) := by
    change
      classifiedRetainedTerminalData
          (routeTerminalVector
            (scalePolyline retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes
                formula clauseIndex literalIndex))) =
        _
    rw [routeTerminalVector_scalePolyline]
    exact
      classifiedRetainedTerminalData_scale_of_classified
        retainedAngularFanSourceClearanceFactor_pos classified'
  rw [terminalDataScale]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
