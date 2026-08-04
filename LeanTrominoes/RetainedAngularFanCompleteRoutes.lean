import LeanTrominoes.RetainedAngularFanOccurrenceSplice
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplit
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitRoutes

/-!
# Complete refined retained angular-fan routes

The copied-source clauses of the fixed-eight split use the retained
source-to-fan splices.  The appended implication-cycle clauses use the
existing certified Figure 7 routes, uniformly scaled by the same factor
eight as the local fan spokes.

This file assembles those two indexed families and defines the correspondingly
scaled positioned formula and variable placement.  Later geometric layers can
therefore reason about one total incidence-route lookup.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- The positioned fixed-eight formula at the factor-eight routing
refinement used by the retained angular fans. -/
def retainedAngularFanRefinedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF (ThreeOccurrenceVariable Variable) :=
  (PeriodicEightOccurrenceSplitPositioned.formula
    source placement
    (occurrencePortsOfAngularOrder
      source.erase
      (angularOccurrenceOrder source.erase routes))).scale
        retainedTerminalFanRoutingRefinement

/-- Variable placement paired with `retainedAngularFanRefinedFormula`. -/
def retainedAngularFanRefinedPlacement
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable Variable) :=
  (PeriodicEightOccurrenceSplitPositioned.placement
    placement).scale retainedTerminalFanRoutingRefinement

/-- Complete refined route family: copied source incidences followed by
scaled local implication-cycle routes. -/
def retainedAngularFanSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    if clauseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source
          (occurrencePortsOfAngularOrder
            source.erase
            (angularOccurrenceOrder
              source.erase routes))).length
    then
      retainedAngularFanSplicedOccurrenceRoutes
        source placement routes clauseIndex literalIndex
    else
      scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes source placement
          (clauseIndex -
            (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
              source
              (occurrencePortsOfAngularOrder
                source.erase
                (angularOccurrenceOrder
                  source.erase routes))).length)
          literalIndex)

/-- Before the append boundary, the complete family is the retained
copied-source splice family. -/
theorem retainedAngularFanSplicedIncidenceRoutes_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (occurrenceIndex :
      clauseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source
          (occurrencePortsOfAngularOrder
            source.erase
            (angularOccurrenceOrder
              source.erase routes))).length) :
    retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex =
      retainedAngularFanSplicedOccurrenceRoutes
        source placement routes clauseIndex literalIndex := by
  simp [retainedAngularFanSplicedIncidenceRoutes,
    occurrenceIndex]

/-- In the appended suffix, the complete family is exactly the scaled
certified implication-cycle family. -/
theorem retainedAngularFanSplicedIncidenceRoutes_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (cycleIndex literalIndex : Nat) :
    retainedAngularFanSplicedIncidenceRoutes
        source placement routes
        ((PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
            source
            (occurrencePortsOfAngularOrder
              source.erase
              (angularOccurrenceOrder
                source.erase routes))).length +
          cycleIndex)
        literalIndex =
      scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes source placement
          cycleIndex literalIndex) := by
  simp [retainedAngularFanSplicedIncidenceRoutes]

/-- Refinement changes only physical coordinates, not the logical
fixed-eight formula. -/
@[simp]
theorem retainedAngularFanRefinedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedAngularFanRefinedFormula
      source placement routes).erase =
      PeriodicEightOccurrenceSplit.formula
        source.erase
        (occurrencePortsOfAngularOrder
          source.erase
          (angularOccurrenceOrder source.erase routes)) := by
  simp [retainedAngularFanRefinedFormula]

/-- Retained fan refinement preserves clause nonemptiness. -/
theorem retainedAngularFanRefinedFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ []) :
    ∀ clause ∈
        (retainedAngularFanRefinedFormula
          source placement routes).clauses,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rw [retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨unscaledClause, unscaledClauseMember, rfl⟩
  simpa using
    PeriodicEightOccurrenceSplitPositioned.formula_clausesNonempty
      source placement
      (occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes))
      sourceClausesNonempty unscaledClause unscaledClauseMember

/-- Positive source period gives a positive refined split period. -/
theorem retainedAngularFanRefinedPlacement_period_pos
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period) :
    0 < (retainedAngularFanRefinedPlacement placement).period := by
  simp only [retainedAngularFanRefinedPlacement,
    PeriodicVariablePlacement.scale_period]
  exact Nat.mul_pos
    (by simp [retainedTerminalFanRoutingRefinement])
    (PeriodicEightOccurrenceSplitPositioned.placement_period_pos
      placement periodPositive)

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Factor-eight positioned retained split used by the complete angular-fan
router. -/
def retainedDrawingRefinedEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedAngularFanRefinedFormula
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)

/-- Placement paired with the factor-eight positioned retained split. -/
def retainedDrawingRefinedEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedAngularFanRefinedPlacement
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)

/-- Complete retained route family for the factor-eight fixed-eight split. -/
def retainedDrawingRefinedEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedAngularFanSplicedIncidenceRoutes
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)

/-- The refined positioned formula has exactly the established retained
fixed-eight logical erasure. -/
@[simp]
theorem
    retainedDrawingRefinedEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingRefinedEightOccurrenceSplitPositionedFormula
      source).erase =
      retainedDrawingEightOccurrenceSplitFormula source := by
  simp [retainedDrawingRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanRefinedFormula,
    retainedDrawingEightOccurrenceSplitFormula,
    retainedDrawingAngularOccurrencePorts,
    retainedDrawingAngularOccurrenceOrder,
    retainedPlanarSATFormula]

/-- The refined retained fixed-eight placement has positive period. -/
theorem retainedDrawingRefinedEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedDrawingRefinedEightOccurrenceSplitPlacement
        source).period := by
  exact retainedAngularFanRefinedPlacement_period_pos
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (by
      simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
        wrappedDrawingPeriodicPlanarSATPlacement] using
        drawingPeriodicPlanarSATPlacement_period_pos source)

end PeriodicOrthocrossing
end LeanTrominoes
