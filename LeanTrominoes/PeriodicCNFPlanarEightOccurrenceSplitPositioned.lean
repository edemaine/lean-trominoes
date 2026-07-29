import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplit

/-!
# Positioned fixed-eight occurrence splitting

This module places the separator-enhanced Figure 7 implication ring in a
uniform `24 × 24` refinement macrocell around each source variable.  Its positioned
formula erases exactly to the verified semantic fixed-eight construction,
and its variable placement uses the certified local ring coordinates.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicThreeSATThree

def refinementScale : Int := 24

def macroOrigin {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) : Cell :=
  Cell.sub
    (Cell.scale refinementScale (sourcePlacement.position atom))
    (12, 12)

def occurrenceVariablePosition {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrence : ThreeOccurrenceVariable Variable) : Cell :=
  Cell.add
    (macroOrigin sourcePlacement occurrence.1)
    (OccurrenceSplitRing.ringVariablePosition
      (PeriodicEightOccurrenceSplit.ringVertexOfIndex
        occurrence.2.1))

def occurrenceClause {Variable : Type*}
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause (ThreeOccurrenceVariable Variable) where
  position := Cell.scale refinementScale clause.position
  literals :=
    PeriodicEightOccurrenceSplit.occurrenceClause
      occurrencePorts clauseIndex clause.literals

def occurrenceClauses {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    List (PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)) :=
  source.clauses.zipIdx.map fun taggedClause =>
    occurrenceClause occurrencePorts
      taggedClause.2 taggedClause.1

def cycleClause {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (taggedClause :
      PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) :
    PositionedPeriodicClause (ThreeOccurrenceVariable Variable) where
  position :=
    Cell.add (macroOrigin sourcePlacement atom)
      (OccurrenceSplitRing.cycleClausePosition
        (presentedCycleVertices.getD
          taggedClause.2 .separator))
  literals := taggedClause.1

def cycleClausesFor {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    List (PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)) :=
  (PeriodicEightOccurrenceSplit.cycleClausesFor atom).zipIdx.map
    (cycleClause sourcePlacement atom)

def allCycleClauses {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    List (PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.sourceVariables source.erase).flatMap
    (cycleClausesFor sourcePlacement)

def formula {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    PositionedPeriodicCNF (ThreeOccurrenceVariable Variable) :=
  ⟨occurrenceClauses source occurrencePorts ++
    allCycleClauses source sourcePlacement⟩

def placement {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement (ThreeOccurrenceVariable Variable) where
  period := refinementScale.toNat * sourcePlacement.period
  position := occurrenceVariablePosition sourcePlacement

@[simp]
theorem occurrenceClauses_literals {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (occurrenceClauses source occurrencePorts).map
        PositionedPeriodicClause.literals =
      PeriodicEightOccurrenceSplit.occurrenceClauses
        source.erase occurrencePorts := by
  simp [occurrenceClauses, occurrenceClause,
    PeriodicEightOccurrenceSplit.occurrenceClauses,
    PositionedPeriodicCNF.erase, List.zipIdx_map,
    List.map_map, Function.comp_def]

@[simp]
theorem cycleClausesFor_literals {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (cycleClausesFor sourcePlacement atom).map
        PositionedPeriodicClause.literals =
      PeriodicEightOccurrenceSplit.cycleClausesFor atom := by
  simp [cycleClausesFor, cycleClause, List.map_map,
    Function.comp_def]

@[simp]
theorem allCycleClauses_literals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    (allCycleClauses source sourcePlacement).map
        PositionedPeriodicClause.literals =
      PeriodicEightOccurrenceSplit.allCycleClauses source.erase := by
  simp [allCycleClauses,
    PeriodicEightOccurrenceSplit.allCycleClauses,
    List.map_flatMap]

@[simp]
theorem erase_formula {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (formula source sourcePlacement occurrencePorts).erase =
      PeriodicEightOccurrenceSplit.formula
        source.erase occurrencePorts := by
  simp [formula, PositionedPeriodicCNF.erase,
    PeriodicEightOccurrenceSplit.formula]

theorem placement_period_pos {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourcePeriodPositive : 0 < sourcePlacement.period) :
    0 < (placement sourcePlacement).period := by
  simpa [placement, refinementScale] using
    Nat.mul_pos (by decide : 0 < 24) sourcePeriodPositive

@[simp]
theorem occurrenceVariablePosition_copy {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (port : Port) :
    occurrenceVariablePosition sourcePlacement
        (PeriodicEightOccurrenceSplit.copy atom port) =
      Cell.add (macroOrigin sourcePlacement atom)
        (OccurrenceSplitRing.variablePosition port) := by
  cases port <;> rfl

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

def drawingEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.formula
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
      (drawingSemanticAngularOccurrenceOrder formula))

def drawingEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicEightOccurrenceSplitPositioned.placement
    (wrappedDrawingPeriodicPlanarSATPlacement formula)

@[simp]
theorem drawingEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingEightOccurrenceSplitPositionedFormula formula).erase =
      drawingEightOccurrenceSplitFormula formula := by
  unfold drawingEightOccurrenceSplitPositionedFormula
    drawingEightOccurrenceSplitFormula
  rw [PeriodicEightOccurrenceSplitPositioned.erase_formula,
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]

end PeriodicOrthocrossing
end LeanTrominoes
