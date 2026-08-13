/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOccurrenceSeparation

/-!
# Explicit models for public final copied-source routes

The public coordinated route family is defined by nested selector, clause,
literal, and singleton-prefix tests.  At a genuine copied-source incidence,
all lookups succeed and only three geometric models remain:

* a successful selector uses the complete direct Figure 7 atlas route;
* a failed selector with a singleton source prefix uses the escaped fallback;
* every other failed selector uses the ordinary fallback.

This file names the ordinary and policy-selected fallback models and proves
the public lookup equal to the appropriate explicit model.  Subsequent
cross-clause separation arguments can therefore work entirely with geometry,
without repeating the total-family lookup normalization.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The explicit ordinary source-boundary splice joined to its unchanged
Figure 7 occurrence suffix. -/
def retainedFinalOrdinaryFallbackOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) :
    List Cell :=
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
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  joinAtEndpoint
    (retainedAngularFanSplicedBoundaryRoute
      (scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute)
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal)
      slot)
    (scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex))

/-- The explicit fallback model selected by the public singleton-prefix
policy. -/
def retainedFinalFallbackOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) :
    List Cell :=
  if
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1 then
    retainedFinalEscapedFallbackOccurrenceRoute
      formula
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex
  else
    retainedFinalOrdinaryFallbackOccurrenceRoute
      formula clause literal clauseIndex literalIndex

/-- At a genuine copied-source incidence, the established uncoordinated
route is exactly the named ordinary fallback model. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_ordinaryFallbackOccurrenceRoute
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
      retainedFinalOrdinaryFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex := by
  simpa [retainedFinalOrdinaryFallbackOccurrenceRoute] using
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- A successful public lookup is exactly its complete direct Figure 7
atlas route. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
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
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      choice.completeFigure7Route
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have scaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? =
        some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceSome scaledClauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceSome

/-- A failed public lookup is exactly the ordinary-or-escaped fallback
chosen by the singleton-prefix policy. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedFinalFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex := by
  by_cases prefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1
  · rw [retainedFinalFallbackOccurrenceRoute, if_pos prefixLength]
    have scaledClauseMember :
        (clause.scale retainedAngularFanSourceClearanceFactor,
            clauseIndex) ∈
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
      rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(clause, clauseIndex), clauseMember, rfl⟩
    have scaledClauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
    have literalLookup :
        (clause.scale retainedAngularFanSourceClearanceFactor).literals[
            literalIndex]? =
          some literal := by
      simpa using
        (List.mem_zipIdx_iff_getElem?).mp literalMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
        formula clauseIndex literalIndex
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal choiceNone prefixLength
        scaledClauseLookup literalLookup
  · rw [retainedFinalFallbackOccurrenceRoute, if_neg prefixLength]
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
        formula clauseIndex literalIndex choiceNone prefixLength]
    exact
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_ordinaryFallbackOccurrenceRoute
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
