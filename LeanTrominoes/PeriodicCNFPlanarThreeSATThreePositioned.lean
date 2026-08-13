/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree

/-!
# Positioned periodic occurrence splitting

`PlanarThreeSAT.EmbeddedClause` is suitable for finite gadget truth tables,
but it deliberately omits periodic literal offsets.  Occurrence splitting is
performed after the routed formula has been periodicized, so this file uses a
small position-carrying periodic representation instead.

Erasing positions from the construction below gives exactly
`PeriodicThreeSATThree.formula`.  Thus the positioned layer reuses the
existing width, occurrence, and satisfiability proofs without maintaining a
second Boolean reduction.
-/

namespace LeanTrominoes

/-- A periodic clause together with the drawing-grid position of its clause
vertex. -/
structure PositionedPeriodicClause (Variable : Type*) where
  position : Cell
  literals : PeriodicClause Variable
  deriving DecidableEq, Repr

/-- A finite positioned presentation of a periodic CNF. -/
structure PositionedPeriodicCNF (Variable : Type*) where
  clauses : List (PositionedPeriodicClause Variable)
  deriving DecidableEq, Repr

namespace PositionedPeriodicCNF

/-- Forget all drawing positions. -/
def erase {Variable : Type*}
    (formula : PositionedPeriodicCNF Variable) :
    PeriodicCNF Variable :=
  ⟨formula.clauses.map PositionedPeriodicClause.literals⟩

/-- Rename every protovariable while retaining offsets and positions. -/
def rename {Source Target : Type*}
    (variableMap : Source → Target)
    (formula : PositionedPeriodicCNF Source) :
    PositionedPeriodicCNF Target :=
  ⟨formula.clauses.map fun clause =>
    ⟨clause.position, clause.literals.map fun literal =>
      ⟨variableMap literal.atom, literal.offset, literal.value⟩⟩⟩

@[simp]
theorem erase_rename {Source Target : Type*}
    (variableMap : Source → Target)
    (formula : PositionedPeriodicCNF Source) :
    (formula.rename variableMap).erase =
      ⟨formula.erase.clauses.map fun clause =>
        clause.map fun literal =>
          ⟨variableMap literal.atom, literal.offset, literal.value⟩⟩ := by
  cases formula
  simp [rename, erase, List.map_map, Function.comp_def]

end PositionedPeriodicCNF

namespace PeriodicThreeSATThreePositioned

/-- Leave enough integer-grid room around every old variable vertex for all
syntactic occurrence copies in the finite presentation. -/
def refinementScale {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) : Int :=
  2 * source.erase.variableOccurrences.length + 4

/-- Position the copy of one original clause in the refined drawing. -/
def occurrenceClause {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause (ThreeOccurrenceVariable Variable) where
  position := Cell.scale (refinementScale source) clause.position
  literals :=
    PeriodicThreeSATThree.occurrenceClause
      clauseIndex clause.literals

/-- All original clause vertices, with every literal replaced by its
syntactic occurrence copy. -/
def occurrenceClauses {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    List
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)) :=
  source.clauses.zipIdx.map fun taggedClause =>
    occurrenceClause source taggedClause.2 taggedClause.1

/-- A deterministic position for an occurrence-copy variable in the refined
macrocell of its original variable. -/
def occurrenceVariablePosition {Variable : Type*}
    [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (copy : ThreeOccurrenceVariable Variable) : Cell :=
  let copyIndex :=
    (PeriodicThreeSATThree.occurrenceVariables
      source.erase copy.1).idxOf copy
  Cell.add
    (Cell.scale (refinementScale source)
      (variablePosition copy.1))
    (2 * copyIndex + 1, 1)

/-- Place one implication clause in the refined macrocell of the original
variable whose copies it connects. -/
def cycleClause {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (atom : Variable) (cycleIndex : Nat)
    (clause :
      PeriodicClause (ThreeOccurrenceVariable Variable)) :
    PositionedPeriodicClause (ThreeOccurrenceVariable Variable) where
  position :=
    Cell.add
      (Cell.scale (refinementScale source) (variablePosition atom))
      (2 * cycleIndex + 2, 2)
  literals := clause

/-- The positioned directed implication cycle for one original
protovariable. -/
def cycleClausesFor {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (atom : Variable) :
    List
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.cycleClauses
      (PeriodicThreeSATThree.occurrenceVariables
        source.erase atom)).zipIdx.map fun taggedClause =>
    cycleClause source variablePosition atom
      taggedClause.2 taggedClause.1

/-- All positioned implication cycles. -/
def allCycleClauses {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell) :
    List
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.sourceVariables source.erase).flatMap fun atom =>
    cycleClausesFor source variablePosition atom

/-- The positioned post-planarization occurrence split. -/
def formula {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell) :
    PositionedPeriodicCNF (ThreeOccurrenceVariable Variable) :=
  ⟨occurrenceClauses source ++
    allCycleClauses source variablePosition⟩

@[simp]
theorem occurrenceClauses_literals {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    (occurrenceClauses source).map
        PositionedPeriodicClause.literals =
      PeriodicThreeSATThree.occurrenceClauses source.erase := by
  simp [occurrenceClauses, occurrenceClause,
    PeriodicThreeSATThree.occurrenceClauses,
    PositionedPeriodicCNF.erase, List.zipIdx_map,
    List.map_map, Function.comp_def]

@[simp]
theorem cycleClausesFor_literals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell)
    (atom : Variable) :
    (cycleClausesFor source variablePosition atom).map
        PositionedPeriodicClause.literals =
      PeriodicThreeSATThree.cycleClauses
        (PeriodicThreeSATThree.occurrenceVariables
          source.erase atom) := by
  simpa [cycleClausesFor, cycleClause,
    List.map_map, Function.comp_def] using
      List.zipIdx_map_fst 0
        (PeriodicThreeSATThree.cycleClauses
          (PeriodicThreeSATThree.occurrenceVariables
            source.erase atom))

@[simp]
theorem allCycleClauses_literals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell) :
    (allCycleClauses source variablePosition).map
        PositionedPeriodicClause.literals =
      PeriodicThreeSATThree.allCycleClauses source.erase := by
  simp [allCycleClauses,
    PeriodicThreeSATThree.allCycleClauses,
    List.map_flatMap]

/-- Erasing the positioned construction gives exactly the verified periodic
occurrence-splitting formula. -/
@[simp]
theorem erase_formula {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (variablePosition : Variable → Cell) :
    (formula source variablePosition).erase =
      PeriodicThreeSATThree.formula source.erase := by
  simp [formula, PositionedPeriodicCNF.erase,
    PeriodicThreeSATThree.formula]

end PeriodicThreeSATThreePositioned

namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Recover the fixed crossover variable corresponding to one scoped
internal role. -/
def crossoverInternalVariable :
    CrossoverInternal → CrossoverVariable
  | .aInnerLeft => .aInnerLeft
  | .upperLeft => .upperLeft
  | .lowerLeft => .lowerLeft
  | .bInnerTop => .bInnerTop
  | .center => .center
  | .bInnerBottom => .bInnerBottom
  | .upperRight => .upperRight
  | .lowerRight => .lowerRight
  | .aInnerRight => .aInnerRight

/-- Canonical drawing position of each routed periodic SAT protovariable.
Translated occurrences are recovered by adding the literal's periodic
offset times the drawing period. -/
def drawingPeriodicPlanarSATVariablePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicPlanarSATVariable Variable → Cell
  | .terminal indexed endpoint =>
      SegmentTerminal.position
        (PeriodicCNF.incidenceGraph formula)
        ⟨indexed, (0, 0), endpoint⟩
  | .boundary boundary =>
      boundary.position
  | .atom atom =>
      Cell.add
        (liftedIncidenceVertexMacroOrigin formula
          (.variable atom) (0, 0))
        duplicatorArmCenterPosition
  | .crossoverInternal (crossing, internal) =>
      Cell.add (crossingMacroOrigin crossing)
        (CrossoverVariable.position
          (crossoverInternalVariable internal))

/-- Attach the original embedded clause positions while periodicizing their
literals. -/
def positionPeriodicizedPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula :
      List (EmbeddedClause (PlanarSATVariable Variable))) :
    PositionedPeriodicCNF
      (PeriodicPlanarSATVariable Variable) :=
  ⟨finiteFormula.map fun clause =>
    ⟨clause.position, periodicizePlanarSATClause formula clause⟩⟩

@[simp]
theorem positionPeriodicizedPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula :
      List (EmbeddedClause (PlanarSATVariable Variable))) :
    (positionPeriodicizedPlanarSATFormula
      formula finiteFormula).erase =
      ⟨finiteFormula.map
        (periodicizePlanarSATClause formula)⟩ := by
  simp [positionPeriodicizedPlanarSATFormula,
    PositionedPeriodicCNF.erase,
    List.map_map, Function.comp_def]

/-- The positioned periodic routed formula, before the opaque wrapper used
by occurrence accounting. -/
def drawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarSATVariable Variable) :=
  positionPeriodicizedPlanarSATFormula
    formula (drawingPlanarSATFormula formula)

@[simp]
theorem drawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarSATFormula formula).erase =
      drawingPeriodicPlanarSATFormula formula := by
  exact positionPeriodicizedPlanarSATFormula_erase
    formula (drawingPlanarSATFormula formula)

/-- Put the positioned routed formula behind the same opaque variable
wrapper used by the semantic occurrence-splitting layer. -/
def wrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (drawingPositionedPeriodicPlanarSATFormula formula).rename
    WrappedPeriodicVariable.mk

@[simp]
theorem wrappedDrawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase =
      wrappedDrawingPeriodicPlanarSATFormula formula := by
  rw [wrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_rename,
    drawingPositionedPeriodicPlanarSATFormula_erase]
  rfl

/-- Positioned version of the post-planarization occurrence split. -/
def drawingPositionedPeriodicPlanarThreeSATThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  PeriodicThreeSATThreePositioned.formula
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
    (fun wrapped =>
      drawingPeriodicPlanarSATVariablePosition
        formula wrapped.original)

/-- The positioned occurrence split erases exactly to the already verified
logical formula. -/
@[simp]
theorem drawingPositionedPeriodicPlanarThreeSATThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPositionedPeriodicPlanarThreeSATThreeFormula formula).erase =
      drawingPeriodicPlanarThreeSATThreeFormula formula := by
  simp [drawingPositionedPeriodicPlanarThreeSATThreeFormula,
    drawingPeriodicPlanarThreeSATThreeFormula]

end PeriodicOrthocrossing
end LeanTrominoes
