import LeanTrominoes.RetainedAngularFanFinalMixedOccurrenceAssembly
import LeanTrominoes.RetainedAngularFanFinalMixedOuterSelection
import LeanTrominoes.RetainedAngularFanFinalMixedStrictOrder
import LeanTrominoes.RetainedAngularFanFinalMixedCenter
import LeanTrominoes.RetainedAngularFanFinalStrictEscape

/-!
# Ordered mixed occurrence-route assembly

Strict order at the common outer-fan center separates the selected direct
prefix from the router-selected fallback outer replacement.  Combining that
fact with the retained source corridor closes the fallback boundary, and the
existing Figure 7 suffix certificates then close the complete occurrence
pair.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- A strict-order outer certificate and source corridor separate a complete
non-routed direct occurrence from a cross-clause fallback occurrence. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor_order
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
    (kindNe : choice.kind ≠ .routedClause)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (corridor :
      SourcePrefixCorridorSeparated
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1)
    (angularOrder :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData
          (routeTerminalVector rawRoute)
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex
      let secondSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral secondClauseIndex secondLiteralIndex
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        rawTerminal.1 firstSlot secondSlot)
    (centersEqual :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            rawRoute).getLastD (0, 0)))
    (fallbackLengthPositive :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex
      0 < (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)).2)
    (fallbackEscapeStrict :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData
          (routeTerminalVector rawRoute)
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor rawTerminal)) :
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
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor_outer
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      choiceLookup kindNe secondChoiceNone clauseIndicesDifferent corridor
  exact
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalCoordinatedFallbackOuterReplacement_of_order
      formula secondLiteral secondClauseIndex secondLiteralIndex choice
      (retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      angularOrder centersEqual fallbackLengthPositive fallbackEscapeStrict

/-- For a same-center cross-clause mixed pair, the source corridor is the
only remaining premise: final occurrence order, physical center equality,
terminal positivity, and escape room are all automatic. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor
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
    (kindNe : choice.kind ≠ .routedClause)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)
    (corridor :
      SourcePrefixCorridorSeparated
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1) :
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
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor_order
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      choiceLookup kindNe secondChoiceNone clauseIndicesDifferent corridor
  · exact
      retainedFinalDirectFallback_strictAngularOrderCompatible_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceLookup secondChoiceNone
        clauseIndicesDifferent centersEqual
  · exact
      retainedFinalDirectFallback_positionedFanCenters_eq_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceLookup centersEqual
  · exact
      finalCoordinatedSourceRoute_terminal_length_positive
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  · exact
      finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember

/-- For a same-center cross-clause mixed pair of any direct atlas kind,
strict separation from the fully refined fallback source prefix is sufficient:
final occurrence order supplies separation from the selected fallback outer
replacement, and the generic mixed assembly closes both suffixes. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_sourcePrefix_sameCenter
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
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)
    (sourcePrefixAvoid :
      let firstSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              formula secondClauseIndex secondLiteralIndex))).dropLast) :
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
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_sourcePrefix_outer
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      choiceLookup secondChoiceNone clauseIndicesDifferent
      sourcePrefixAvoid
  exact
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalCoordinatedFallbackOuterReplacement_of_order
      formula secondLiteral secondClauseIndex secondLiteralIndex choice
      (retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalDirectFallback_strictAngularOrderCompatible_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceLookup secondChoiceNone
        clauseIndicesDifferent centersEqual)
      (retainedFinalDirectFallback_positionedFanCenters_eq_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceLookup centersEqual)
      (finalCoordinatedSourceRoute_terminal_length_positive
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember)
      (finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember)

end PeriodicOrthocrossing
end LeanTrominoes
