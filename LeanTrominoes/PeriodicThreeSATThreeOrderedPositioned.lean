import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicThreeSATThreeOrdered

/-!
# Positioned geometry-ordered occurrence splitting

The planar occurrence-splitting cycle must visit copies in the rotation
order of their incidences around the source variable.  The semantic
construction already accepts any per-variable permutation; this file lifts
that parameter to the positioned construction and its variable placement.

The clause coordinates use exactly the same refinement as the original
positioned construction.  Only the order of copies inside each variable
macrocell and the corresponding implication-cycle clauses changes.
-/

namespace LeanTrominoes

namespace PeriodicThreeSATThreePositioned

/-- Position one occurrence copy according to the chosen geometric order
inside its original variable's refined macrocell. -/
def orderedOccurrenceVariablePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase)
    (copy : ThreeOccurrenceVariable Variable) :
    Cell :=
  let copyIndex := (order.copies copy.1).idxOf copy
  Cell.add
    (Cell.scale (refinementScale source)
      (variablePosition copy.1))
    (2 * copyIndex + 1, 1)

/-- One positioned implication cycle using the chosen geometric order. -/
def orderedCycleClausesFor
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase)
    (atom : Variable) :
    List
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.cycleClauses
      (order.copies atom)).zipIdx.map fun taggedClause =>
    cycleClause source variablePosition atom
      taggedClause.2 taggedClause.1

/-- All positioned implication cycles in geometry-selected order. -/
def orderedAllCycleClauses
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    List
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.sourceVariables source.erase).flatMap fun atom =>
    orderedCycleClausesFor source variablePosition order atom

/-- Positioned occurrence splitting whose variable cycles follow a chosen
geometric order. -/
def orderedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable Variable) :=
  ⟨occurrenceClauses source ++
    orderedAllCycleClauses source variablePosition order⟩

@[simp]
theorem orderedCycleClausesFor_literals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase)
    (atom : Variable) :
    (orderedCycleClausesFor
      source variablePosition order atom).map
        PositionedPeriodicClause.literals =
      PeriodicThreeSATThree.cycleClauses
        (order.copies atom) := by
  simp [orderedCycleClausesFor, cycleClause,
    List.map_map, Function.comp_def]

@[simp]
theorem orderedAllCycleClauses_literals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    (orderedAllCycleClauses
      source variablePosition order).map
        PositionedPeriodicClause.literals =
      PeriodicThreeSATThree.orderedCycleClauses
        source.erase order := by
  simp [orderedAllCycleClauses,
    PeriodicThreeSATThree.orderedCycleClauses,
    List.map_flatMap]

/-- Erasing positions yields exactly the semantic ordered construction. -/
@[simp]
theorem erase_orderedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    (orderedFormula source variablePosition order).erase =
      PeriodicThreeSATThree.orderedFormula
        source.erase order := by
  simp [orderedFormula, PositionedPeriodicCNF.erase,
    PeriodicThreeSATThree.orderedFormula]

/-- Every positioned geometric order preserves satisfiability exactly. -/
theorem orderedFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    source.erase.Satisfiable ↔
      (orderedFormula source variablePosition order).erase.Satisfiable := by
  rw [erase_orderedFormula]
  exact PeriodicThreeSATThree.orderedSatisfiable_iff
    source.erase order

/-- The geometry-ordered positioned construction retains the
occurrence-three bound. -/
theorem orderedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    (orderedFormula source variablePosition order).erase.OccurrencesAtMost
      3 := by
  rw [erase_orderedFormula]
  exact PeriodicThreeSATThree.orderedFormula_occurrencesAtMostThree
    source.erase order

/-- Presentation order recovers the original positioned formula
definitionally. -/
@[simp]
theorem orderedFormula_presentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell) :
    orderedFormula source variablePosition
        (PeriodicThreeSATThree.OccurrenceOrder.presentation
          source.erase) =
      formula source variablePosition := by
  rfl

/-- Presentation order likewise recovers the original copy positions. -/
@[simp]
theorem orderedOccurrenceVariablePosition_presentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (copy : ThreeOccurrenceVariable Variable) :
    orderedOccurrenceVariablePosition
        source variablePosition
        (PeriodicThreeSATThree.OccurrenceOrder.presentation
          source.erase)
        copy =
      occurrenceVariablePosition source variablePosition copy := by
  rfl

/-- Variable placement induced by geometry-ordered occurrence splitting. -/
def orderedPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order :
      PeriodicThreeSATThree.OccurrenceOrder source.erase) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable Variable) where
  period := (refinementScale source).toNat * sourcePlacement.period
  position :=
    orderedOccurrenceVariablePosition
      source sourcePlacement.position order

/-- Presentation order recovers the established occurrence-splitting
placement. -/
@[simp]
theorem orderedPlacement_presentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    orderedPlacement source sourcePlacement
        (PeriodicThreeSATThree.OccurrenceOrder.presentation
          source.erase) =
      placement source sourcePlacement := by
  rfl

end PeriodicThreeSATThreePositioned

end LeanTrominoes
