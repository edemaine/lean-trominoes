import LeanTrominoes.RetainedAngularFanFinalMixedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-!
# Public final mixed occurrence separation

The explicit mixed theorem uses the selected direct occurrence and the
ordinary-or-escaped fallback boundary join.  This file identifies those two
models with the total public route lookup, exposing the result at the route
family interface needed by global planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- The named policy-selected fallback model is exactly the selected boundary
prefix joined to its unchanged occurrence suffix. -/
theorem retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) :
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
    retainedFinalFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex =
      joinAtEndpoint
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula literal clauseIndex literalIndex)
        suffix := by
  dsimp only
  rw [retainedFinalFallbackOccurrenceRoute,
    retainedFinalCoordinatedFallbackBoundaryPrefix]
  by_cases prefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1
  · rw [if_pos prefixLength, if_pos prefixLength]
    rfl
  · rw [if_neg prefixLength, if_neg prefixLength]
    rfl

/-- At the public total-route interface, a successful non-routed direct
choice strictly avoids a same-center failed choice from another clause. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_first_choice_some_second_none_of_sameCenter
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
          formula directClauseIndex directLiteralIndex = some choice)
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
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex) := by
  have directPublicEq :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember directLiteralMember choiceLookup
  have directModelEq :=
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember directLiteralMember choiceLookup
  have fallbackPublicEq :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      fallbackClauseMember fallbackLiteralMember fallbackChoiceNone
  have fallbackModelEq :=
    retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
      formula fallbackClause fallbackLiteral
      fallbackClauseIndex fallbackLiteralIndex
  rw [directPublicEq, ← directModelEq,
    fallbackPublicEq, fallbackModelEq]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
      centersEqual

/-- Symmetric public mixed separation when the failed choice is listed
first. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_first_choice_none_second_some_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {fallbackClause directClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackClauseIndex directClauseIndex : Nat}
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {fallbackLiteral directLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {fallbackLiteralIndex directLiteralIndex : Nat}
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (kindNe : choice.kind ≠ .routedClause)
    (clauseIndicesDifferent :
      fallbackClauseIndex ≠ directClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula directClauseIndex directLiteralIndex) :=
  (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_strictlyAvoid_of_first_choice_some_second_none_of_sameCenter
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty choice
    directClauseMember fallbackClauseMember
    directLiteralMember fallbackLiteralMember
    choiceLookup kindNe fallbackChoiceNone
    (Ne.symm clauseIndicesDifferent) centersEqual.symm).symm

end PeriodicOrthocrossing
end LeanTrominoes
