/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedAngularFanSourceScaledDrawing

/-!
# Coordinated direct routes in the final fixed-eight family

The established source-scaled fixed-eight route family uses the ordinary
outer fan for every copied source incidence.  Direct clauses need the
clause-coordinated escape prefixes instead.  This file performs that one
specialized substitution.

The final metadata selector returns `none` for non-direct source clauses,
invalid indices, and appended implication-cycle clauses.  Those cases retain
the established route definition exactly.  A successful direct choice is
joined to the same scaled Figure 7 occurrence suffix as the ordinary route,
so the logical formula and variable-side endpoint are unchanged.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The final retained source before source-clearance scaling. -/
def finalCoordinatedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula

/-- The final retained source placement before source-clearance scaling. -/
def finalCoordinatedPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicPlanarSATVariable Variable) :=
  retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula

/-- The final retained source route family before source-clearance scaling. -/
def finalCoordinatedSourceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    formula

/-- At external shift zero, the physical occurrence notation is exactly the
route stored by the final coordinated source family. -/
theorem finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex =
      finalGaugedRouteOccurrence
        formula clauseIndex literalIndex (0, 0) := by
  unfold finalCoordinatedSourceRoutes finalGaugedRouteOccurrence
  simp [PeriodicVariablePlacement.translation, Cell.scale]

/-- The occurrence slot selected after source-clearance scaling.  Positive
scaling preserves the angular order, but retaining this definition in the
scaled source makes the eventual suffix splice definitionally identical to
the established route family. -/
def retainedFinalCoordinatedOccurrenceSlot
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) :
    RetainedTerminalSlot :=
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  boundedRetainedTerminalSlot
    (angularOccurrenceIndex
      (angularOccurrenceOrder source.erase routes)
      literal clauseIndex literalIndex)

/-- One selected direct incidence, joined to the unchanged source-scaled
Figure 7 occurrence suffix. -/
def retainedFinalCoordinatedDirectOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice)
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
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  joinAtEndpoint
    (choice.completeRoute slot)
    (scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        clause literal clauseIndex literalIndex))

/-- One copied-source occurrence using the delayed-lane outer fan and the
unchanged scaled Figure 7 occurrence suffix.  The raw retained route and
its terminal data are source-scaled exactly as in the established family;
only the outer fan waits 64 primitive blocks before selecting its lane. -/
def retainedFinalEscapedFallbackOccurrenceRoute
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
    finalCoordinatedSourceRoutes formula
      clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  joinAtEndpoint
    (retainedAngularFanEscapedSplicedBoundaryRoute
      (scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute)
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal)
      slot)
    (scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        clause literal clauseIndex literalIndex))

/-- Whether a failed direct-source choice needs the delayed-lane fallback:
exactly when deleting its old variable endpoint leaves one source point. -/
def retainedFinalFallbackUsesEscape
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Bool :=
  decide
    ((finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex).dropLast.length = 1)

/-- Total scaled-source clause lookup used by both direct and fallback
branches of the final router. -/
def finalCoordinatedScaledClause?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat) :
    Option
      (PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  ((finalCoordinatedSource formula).scale
    retainedAngularFanSourceClearanceFactor).clauses[clauseIndex]?

/-- Final source-scaled fixed-eight routes with direct copied incidences
replaced by their coordinated choices.  A failed choice with a singleton
deleted-final-point source prefix uses the delayed-lane escaped fan; every
other failed choice or malformed scaled source lookup uses the established
route family. -/
def retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex with
    | none =>
        if retainedFinalFallbackUsesEscape
            formula clauseIndex literalIndex then
          match finalCoordinatedScaledClause? formula clauseIndex with
          | none =>
              retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
                formula clauseIndex literalIndex
          | some clause =>
              match clause.literals[literalIndex]? with
              | none =>
                  retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
                    formula clauseIndex literalIndex
              | some literal =>
                  retainedFinalEscapedFallbackOccurrenceRoute
                    formula clause literal clauseIndex literalIndex
        else
          retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
            formula clauseIndex literalIndex
    | some choice =>
        match finalCoordinatedScaledClause? formula clauseIndex with
        | none =>
            retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
              formula clauseIndex literalIndex
        | some clause =>
            match clause.literals[literalIndex]? with
            | none =>
                retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
                  formula clauseIndex literalIndex
            | some literal =>
                retainedFinalCoordinatedDirectOccurrenceRoute
                  formula choice clause literal
                  clauseIndex literalIndex

/-- A failed direct-source choice with a non-singleton deleted-final-point
prefix leaves the established route unchanged. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (prefixLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length ≠ 1) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex := by
  have routeLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).length ≠ 2 := by
    intro routeLength
    apply prefixLengthNe
    rw [List.length_dropLast, routeLength]
  have escapeFalse :
      retainedFinalFallbackUsesEscape
        formula clauseIndex literalIndex = false := by
    simp [retainedFinalFallbackUsesEscape, routeLengthNe]
  unfold
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
  rw [choiceNone]
  simp only
  rw [escapeFalse]
  simp

/-- A failed direct-source choice with a singleton deleted-final-point
prefix and genuine scaled-source lookups reduces to the delayed-lane
escaped occurrence route. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (prefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1)
    (clauseLookup :
      finalCoordinatedScaledClause?
        formula clauseIndex = some clause)
    (literalLookup :
      clause.literals[literalIndex]? = some literal) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedFinalEscapedFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex := by
  have routeLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).length = 2 := by
    rw [List.length_dropLast] at prefixLength
    omega
  have escapeTrue :
      retainedFinalFallbackUsesEscape
        formula clauseIndex literalIndex = true := by
    simp [retainedFinalFallbackUsesEscape, routeLength]
  unfold
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
  rw [choiceNone]
  simp only
  rw [escapeTrue, clauseLookup]
  simp [literalLookup]

/-- If the scaled copied-source clause lookup fails, the specialized family
uses the established route regardless of the direct-choice result.  This is
the fallback taken by every appended implication-cycle clause. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_clause_none
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (clauseNone :
      finalCoordinatedScaledClause?
        formula clauseIndex = none) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex := by
  unfold
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
  split
  · simp [clauseNone]
  · rw [clauseNone]

/-- Successful selector and scaled source lookups reduce the specialized
family to the explicit coordinated occurrence splice. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (clauseLookup :
      finalCoordinatedScaledClause?
        formula clauseIndex = some clause)
    (literalLookup :
      clause.literals[literalIndex]? = some literal) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice clause literal
        clauseIndex literalIndex := by
  unfold
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
  rw [choiceSome]
  simp only
  rw [clauseLookup]
  simp only
  rw [literalLookup]

end PeriodicOrthocrossing
end LeanTrominoes
