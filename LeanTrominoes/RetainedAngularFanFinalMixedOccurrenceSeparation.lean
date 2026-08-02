import LeanTrominoes.RetainedAngularFanFinalMixedAlignedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedObliqueCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation

/-!
# Complete final mixed occurrence separation

The aligned and oblique source-corridor theorems cover every successful
non-routed direct choice.  Feeding either corridor into the ordered mixed
assembly gives unconditional separation from a same-center cross-clause
fallback occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- A non-routed oblique direct occurrence strictly avoids a same-center
cross-clause fallback occurrence in the final coordinated drawing. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex =
        some choice)
    (kindNe : choice.kind ≠ .routedClause)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned) :
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
    let fallbackSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
      (joinAtEndpoint
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula fallbackLiteral
          fallbackClauseIndex fallbackLiteralIndex)
        fallbackSuffix) := by
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula directClauseIndex directLiteralIndex choice choiceLookup
  have directFinalOblique :
      ¬(⟨polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex),
          (finalCoordinatedSourceRoutes
            formula directClauseIndex directLiteralIndex).getLastD
              (0, 0)⟩ : GridSegment).IsAxisAligned := by
    rw [representedSegment]
    exact directOblique
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
      centersEqual
  exact
    retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_not_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup fallbackChoiceNone clauseIndicesDifferent
      directFinalOblique

/-- Every non-routed successful direct occurrence strictly avoids a
same-center cross-clause fallback occurrence in the final coordinated
drawing. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex =
        some choice)
    (kindNe : choice.kind ≠ .routedClause)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral) :
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
    let fallbackSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
      (joinAtEndpoint
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula fallbackLiteral
          fallbackClauseIndex fallbackLiteralIndex)
        fallbackSuffix) := by
  by_cases directAligned : choice.sourceSegment.IsAxisAligned
  · exact
      retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
        centersEqual directAligned
  · exact
      retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
        centersEqual directAligned

end PeriodicOrthocrossing
end LeanTrominoes
