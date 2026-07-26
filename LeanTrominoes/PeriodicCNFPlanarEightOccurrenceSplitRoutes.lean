import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleIndex
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Endpoint-compatible routes for fixed-eight occurrence splitting

This module equips the positioned Figure 7 formula with a canonical
orthogonal route family.  It proves the exact periodic incidence endpoints
and axis alignment needed by later noncrossing ring-splicing refinements.
-/

namespace LeanTrominoes

namespace PeriodicEightOccurrenceSplitPositioned

/-- Use the generic canonical routes for copied source clauses and the
translated, certified Figure 7 routes for the appended implication-cycle
clauses. -/
def cycleSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    if clauseIndex <
        (occurrenceClauses source occurrencePorts).length
    then
      PositionedPeriodicCNF.orthogonalIncidenceRoutes
        (formula source sourcePlacement occurrencePorts)
        (placement sourcePlacement)
        clauseIndex literalIndex
    else
      allCycleRoutes source sourcePlacement
        (clauseIndex -
          (occurrenceClauses
            source occurrencePorts).length)
        literalIndex

/-- Before the formula append boundary, the spliced family is exactly the
generic canonical family. -/
theorem cycleSplicedIncidenceRoutes_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (clauseIndex literalIndex : Nat)
    (occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length) :
    cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        clauseIndex literalIndex =
      PositionedPeriodicCNF.orthogonalIncidenceRoutes
        (formula source sourcePlacement occurrencePorts)
        (placement sourcePlacement)
        clauseIndex literalIndex := by
  simp [cycleSplicedIncidenceRoutes, occurrenceIndex]

/-- At an index in the appended suffix, the spliced family is exactly the
parallel certified cycle-route lookup. -/
theorem cycleSplicedIncidenceRoutes_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (cycleIndex literalIndex : Nat) :
    cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        ((occurrenceClauses
            source occurrencePorts).length +
          cycleIndex)
        literalIndex =
      allCycleRoutes source sourcePlacement
        cycleIndex literalIndex := by
  simp [cycleSplicedIncidenceRoutes]

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

def drawingEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.orthogonalIncidenceRoutes
    (drawingEightOccurrenceSplitPositionedFormula formula)
    (drawingEightOccurrenceSplitPlacement formula)

/-- The route family that has begun the geometric splice: source incidences
still use canonical detours, while all implication rings use the certified
translated Figure 7 routes. -/
def drawingEightOccurrenceSplitCycleSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicEightOccurrenceSplitPositioned.cycleSplicedIncidenceRoutes
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
      (drawingSemanticAngularOccurrenceOrder formula))

theorem drawingEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 < (drawingEightOccurrenceSplitPlacement formula).period := by
  unfold drawingEightOccurrenceSplitPlacement
  apply PeriodicEightOccurrenceSplitPositioned.placement_period_pos
  exact drawingPeriodicPlanarSATPlacement_period_pos formula

theorem drawingEightOccurrenceSplitIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).RoutesMatch
      (drawingEightOccurrenceSplitPositionedFormula
        formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_routesMatch
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitPlacement_period_pos formula)

theorem drawingEightOccurrenceSplitIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).IsOrthogonal := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_isOrthogonal
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)

end PeriodicOrthocrossing
end LeanTrominoes
