import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
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

/-- The final retained source before source-clearance scaling. -/
private def finalCoordinatedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula

/-- The final retained source placement before source-clearance scaling. -/
private def finalCoordinatedPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicPlanarSATVariable Variable) :=
  retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula

/-- The final retained source route family before source-clearance scaling. -/
private def finalCoordinatedSourceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    formula

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

/-- Final source-scaled fixed-eight routes with direct copied incidences
replaced by their coordinated choices.  Every failed choice or malformed
scaled source lookup falls back to the established route family. -/
def retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex with
    | none =>
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex
    | some choice =>
        match
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).clauses[
                clauseIndex]? with
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

/-- A failed direct-source choice leaves the established route unchanged. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex := by
  simp [retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes,
    choiceNone]

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
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor).clauses[
          clauseIndex]? = some clause)
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
