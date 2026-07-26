import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry
import LeanTrominoes.PlanarThreeSATGadgets

/-!
# Compass-terminal certificates for the fixed planar 3SAT gadgets

Before occurrence splitting, the Figure 8 gadgets may have variables of
degree greater than four and therefore need not admit an orthogonal incidence
drawing.  Their direct clause-to-variable segments nevertheless carry the
rotation system used by the split.

This file packages the finite property that every such direct incidence has
one of the eight permitted terminal directions and verifies it exhaustively
for both fixed Figure 8 templates.  Separation of collinear incidences is
deliberately not required: stable angular sorting assigns those occurrences
adjacent, distinct split ports.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Every displayed clause-to-variable vector in a finite embedded formula
has one of the eight permitted compass directions. -/
def EmbeddedTerminalPortsValid
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) : Prop :=
  ∀ clauseIndex : Fin formula.length,
    ∀ literalIndex :
      Fin (formula.get clauseIndex).literals.length,
      (terminalPort
        (Cell.sub
          (formula.get clauseIndex).position
          (variablePosition
            ((formula.get clauseIndex).literals.get
              literalIndex).1))).isSome

instance {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    Decidable
      (EmbeddedTerminalPortsValid formula variablePosition) := by
  unfold EmbeddedTerminalPortsValid
  infer_instance

/-- Membership-style form of the finite compass certificate. -/
theorem embeddedTerminalPortsValid_iff
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    EmbeddedTerminalPortsValid formula variablePosition ↔
      ∀ clause ∈ formula,
        ∀ literal ∈ clause.literals,
          (terminalPort
            (Cell.sub clause.position
              (variablePosition literal.1))).isSome := by
  constructor
  · intro valid clause clauseMember literal literalMember
    rcases List.mem_iff_get.mp clauseMember with
      ⟨clauseIndex, clauseEqual⟩
    rcases List.mem_iff_get.mp literalMember with
      ⟨literalIndex, literalEqual⟩
    subst clause
    subst literal
    exact valid clauseIndex literalIndex
  · intro valid clauseIndex literalIndex
    exact valid
      (formula.get clauseIndex)
      (List.get_mem formula clauseIndex)
      ((formula.get clauseIndex).literals.get literalIndex)
      (List.get_mem
        (formula.get clauseIndex).literals literalIndex)

/-- Compass validity composes over concatenated embedded formulas. -/
theorem EmbeddedTerminalPortsValid.append
    {Variable : Type*}
    {first second : List (EmbeddedClause Variable)}
    {variablePosition : Variable → Cell}
    (firstValid :
      EmbeddedTerminalPortsValid first variablePosition)
    (secondValid :
      EmbeddedTerminalPortsValid second variablePosition) :
    EmbeddedTerminalPortsValid
      (first ++ second) variablePosition := by
  rw [embeddedTerminalPortsValid_iff] at firstValid secondValid ⊢
  intro clause clauseMember literal literalMember
  rcases List.mem_append.mp clauseMember with
    clauseMember | clauseMember
  · exact firstValid clause clauseMember literal literalMember
  · exact secondValid clause clauseMember literal literalMember

/-- Renaming variables preserves compass validity whenever the supplied
target placement realizes every renamed source position exactly. -/
theorem EmbeddedTerminalPortsValid.rename
    {Source Target : Type*}
    (formula : List (EmbeddedClause Source))
    (sourcePosition : Source → Cell)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (positionsMatch :
      ∀ atom, targetPosition (variableMap atom) =
        sourcePosition atom)
    (valid :
      EmbeddedTerminalPortsValid formula sourcePosition) :
    EmbeddedTerminalPortsValid
      (formula.map fun clause =>
        clause.rename variableMap)
      targetPosition := by
  rw [embeddedTerminalPortsValid_iff] at valid ⊢
  intro renamedClause renamedClauseMember
    renamedLiteral renamedLiteralMember
  rcases List.mem_map.mp renamedClauseMember with
    ⟨clause, clauseMember, rfl⟩
  change
    renamedLiteral ∈
      clause.literals.map
        (fun literal => (variableMap literal.1, literal.2))
      at renamedLiteralMember
  rcases List.mem_map.mp renamedLiteralMember with
    ⟨literal, literalMember, rfl⟩
  simpa [EmbeddedClause.rename, EmbeddedClause.map,
    positionsMatch] using
    valid clause clauseMember literal literalMember

/-- A common translation and positive scale preserve every terminal ray of
an instantiated fixed gadget. -/
theorem EmbeddedTerminalPortsValid.instantiateFormula
    {Source Target : Type*}
    (formula : List (EmbeddedClause Source))
    (sourcePosition : Source → Cell)
    (variableMap : Source → Target)
    (origin : Cell) {factor : Int}
    (factorPositive : 0 < factor)
    (targetPosition : Target → Cell)
    (positionsMatch :
      ∀ atom,
        targetPosition (variableMap atom) =
          Cell.add origin
            (Cell.scale factor (sourcePosition atom)))
    (valid :
      EmbeddedTerminalPortsValid formula sourcePosition) :
    EmbeddedTerminalPortsValid
      (instantiateFormula variableMap origin factor formula)
      targetPosition := by
  rw [embeddedTerminalPortsValid_iff] at valid ⊢
  intro placedClause placedClauseMember
    placedLiteral placedLiteralMember
  rcases List.mem_map.mp placedClauseMember with
    ⟨clause, clauseMember, rfl⟩
  simp only [EmbeddedClause.place, EmbeddedClause.rename,
    EmbeddedClause.map, List.map_map, Function.comp_def]
    at placedLiteralMember
  rcases List.mem_map.mp placedLiteralMember with
    ⟨literal, literalMember, rfl⟩
  simp only [id_eq] at placedLiteralMember ⊢
  have sourceValid :=
    valid clause clauseMember literal literalMember
  have vectorEquality :
      Cell.sub
          ((clause.rename variableMap).place
            origin factor).position
          (targetPosition (variableMap literal.1)) =
        Cell.scale factor
          (Cell.sub clause.position
            (sourcePosition literal.1)) := by
    rw [positionsMatch]
    apply Prod.ext <;>
      simp [EmbeddedClause.place, EmbeddedClause.rename,
        EmbeddedClause.map, Cell.add, Cell.scale, Cell.sub] <;>
      ring
  rw [vectorEquality,
    PeriodicEightOccurrenceSplit.terminalPort_scale
      factorPositive]
  exact sourceValid

namespace EmbeddedCNFIncidenceDrawing

/-- Every genuine route has a nonzero terminal ray on an axis or a
45-degree diagonal. -/
def TerminalPortsValid
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ index : Fin drawing.incidences.length,
    (terminalPort
      (routeTerminalVector
        (drawing.routeAt (drawing.incidenceAt index)))).isSome

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.TerminalPortsValid := by
  unfold TerminalPortsValid incidenceAt incidences routeAt
  infer_instance

end EmbeddedCNFIncidenceDrawing

/-- Direct terminal rays of the fixed Figure 8(b) crossover. -/
def crossoverStraightIncidenceDrawing :
    EmbeddedCNFIncidenceDrawing CrossoverVariable :=
  straightIncidenceDrawing
    crossoverFormula CrossoverVariable.position

/-- All Figure 8(b) incidences use the eight compass ray classes.  Several
variables intentionally have repeated collinear rays; those are retained as
stable angular ties. -/
theorem crossoverStraightIncidenceDrawing_terminalPortsValid :
    crossoverStraightIncidenceDrawing.TerminalPortsValid := by
  native_decide

/-- Membership-style compass certificate for the fixed Figure 8(b)
crossover, ready for affine instantiation. -/
theorem crossoverFormula_embeddedTerminalPortsValid :
    EmbeddedTerminalPortsValid
      crossoverFormula CrossoverVariable.position := by
  native_decide

/-- Direct terminal rays of the fixed Figure 8(a) duplicator. -/
def duplicatorStraightIncidenceDrawing :
    EmbeddedCNFIncidenceDrawing DuplicatorVariable :=
  straightIncidenceDrawing
    duplicatorFormula DuplicatorVariable.position

/-- All Figure 8(a) incidences use the eight compass ray classes. -/
theorem duplicatorStraightIncidenceDrawing_terminalPortsValid :
    duplicatorStraightIncidenceDrawing.TerminalPortsValid := by
  native_decide

/-- Membership-style compass certificate for the fixed Figure 8(a)
duplicator, ready for affine instantiation. -/
theorem duplicatorFormula_embeddedTerminalPortsValid :
    EmbeddedTerminalPortsValid
      duplicatorFormula DuplicatorVariable.position := by
  native_decide

/-- It is enough to check the four displayed clause-to-endpoint rays of one
positioned equality link. -/
theorem equalityInstance_embeddedTerminalPortsValid
    {Variable : Type*}
    (first second : Variable)
    (positions : EqualityPositions)
    (variablePosition : Variable → Cell)
    (forwardFirst :
      (terminalPort
        (Cell.sub positions.forward
          (variablePosition first))).isSome)
    (forwardSecond :
      (terminalPort
        (Cell.sub positions.forward
          (variablePosition second))).isSome)
    (backwardFirst :
      (terminalPort
        (Cell.sub positions.backward
          (variablePosition first))).isSome)
    (backwardSecond :
      (terminalPort
        (Cell.sub positions.backward
          (variablePosition second))).isSome) :
    EmbeddedTerminalPortsValid
      (equalityInstance first second positions)
      variablePosition := by
  rw [embeddedTerminalPortsValid_iff]
  intro clause clauseMember literal literalMember
  simp only [equalityInstance, List.mem_cons,
    List.not_mem_nil, or_false] at clauseMember
  rcases clauseMember with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil,
      or_false] at literalMember
    rcases literalMember with rfl | rfl
    · exact forwardFirst
    · exact forwardSecond
  · simp only [List.mem_cons, List.not_mem_nil,
      or_false] at literalMember
    rcases literalMember with rfl | rfl
    · exact backwardFirst
    · exact backwardSecond

end PlanarThreeSAT
end LeanTrominoes
