/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMIncidenceClassification
import LeanTrominoes.PlanarThreeDMConnectorDrawings
import LeanTrominoes.PlanarX3CClauseDrawing

/-!
# Local drawing interface for the typed periodic 3DM assembly

The global construction uses three finite drawing templates: an ordinary
occurrence module, the fixed-red occurrence detour, and the clause core.
This file exposes them uniformly at the typed-triple level.

For an occurrence module, the endpoint is a temporary local port.  A later
variable-site construction joins continuation ports into the variable cycle
and extends the three connector ports along the source incidence route.  For
a clause triple, the port is already its actual local colored-element
position.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Position of a typed triple inside its local occurrence or clause
template. -/
def tripleLocalPosition {Variable : Type*} :
    Triple Variable → Cell
  | .ordinary _ _ _ triple =>
      VariableOccurrenceTriple.position triple
  | .fixedRed _ _ triple =>
      FixedRedConnectorTriple.position triple
  | .clause _ set =>
      X3CClauseOrthogonal.setPosition set

/-- Temporary endpoint of one colored local route.  For variable modules
this includes continuation and routed connector ports; for clause cores it
is the actual element vertex. -/
def incidencePortPosition {Variable : Type*} :
    Triple Variable → WireColor → Cell
  | .ordinary _ _ variant triple, color =>
      VariableOccurrenceElement.position
        (VariableOccurrence.reference variant triple color)
  | .fixedRed _ _ triple, color =>
      FixedRedConnectorElement.position
        (FixedRedConnector.reference triple color)
  | .clause _ set, color =>
      X3CClauseOrthogonal.elementPosition
        (X3CClauseOrthogonal.reference set color)

/-- Prefix of a global incidence route inside its finite gadget template. -/
def incidenceLocalRoute {Variable : Type*} :
    Triple Variable → WireColor → List Cell
  | .ordinary _ _ variant triple, color =>
      VariableOccurrence.route variant triple color
  | .fixedRed _ _ triple, color =>
      FixedRedConnector.route triple color
  | .clause _ set, color =>
      X3CClauseOrthogonal.route set color

/-- Every typed local route begins at its triple position and ends at its
advertised temporary port. -/
theorem incidenceLocalRoute_endpoints
    {Variable : Type*}
    (triple : Triple Variable) (color : WireColor) :
    (incidenceLocalRoute triple color).head? =
        some (tripleLocalPosition triple) ∧
      (incidenceLocalRoute triple color).getLast? =
        some (incidencePortPosition triple color) := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      have valid := (VariableOccurrence.drawing_isValid variant).1
        (localTriple, color)
      exact valid
  | fixedRed atom slot localTriple =>
      have valid := FixedRedConnector.drawing_isValid.1
        (localTriple, color)
      exact valid
  | clause clauseIndex set =>
      have valid := X3CClauseOrthogonal.drawing_isValid.1
        (set, color)
      exact valid

/-- Every segment of every typed local route is axis-aligned. -/
theorem incidenceLocalRoute_orthogonal
    {Variable : Type*}
    (triple : Triple Variable) (color : WireColor)
    (segment : GridSegment)
    (member :
      segment ∈ gridPolylineSegments
        (incidenceLocalRoute triple color)) :
    segment.IsAxisAligned := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      exact (VariableOccurrence.drawing_isValid variant).2.1
        (localTriple, color) segment member
  | fixedRed atom slot localTriple =>
      exact FixedRedConnector.drawing_isValid.2.1
        (localTriple, color) segment member
  | clause clauseIndex set =>
      exact X3CClauseOrthogonal.drawing_isValid.2.1
        (set, color) segment member

/-- Position in the polarity-normalized outer-face occurrence template, or
in the unchanged clause template. -/
def orientedTripleLocalPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Triple Variable → Cell
  | .ordinary atom slot variant triple =>
      (VariableOccurrence.orientedBoundaryDrawing
        variant (occurrencePolarity source atom slot)).triplePosition triple
  | .fixedRed atom slot triple =>
      (FixedRedConnector.boundaryDrawing
        (occurrencePolarity source atom slot)).triplePosition triple
  | .clause _ set =>
      X3CClauseOrthogonal.setPosition set

/-- Port position in the polarity-normalized local template. -/
def orientedIncidencePortPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Triple Variable → WireColor → Cell
  | .ordinary atom slot variant triple, color =>
      (VariableOccurrence.orientedBoundaryDrawing
        variant (occurrencePolarity source atom slot)).elementPosition
          (VariableOccurrence.reference variant triple color)
  | .fixedRed atom slot triple, color =>
      (FixedRedConnector.boundaryDrawing
        (occurrencePolarity source atom slot)).elementPosition
          (FixedRedConnector.reference triple color)
  | .clause _ set, color =>
      X3CClauseOrthogonal.elementPosition
        (X3CClauseOrthogonal.reference set color)

/-- Route prefix in the polarity-normalized local template. -/
def orientedIncidenceLocalRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Triple Variable → WireColor → List Cell
  | .ordinary atom slot variant triple, color =>
      (VariableOccurrence.orientedBoundaryDrawing
        variant (occurrencePolarity source atom slot)).route triple color
  | .fixedRed atom slot triple, color =>
      (FixedRedConnector.boundaryDrawing
        (occurrencePolarity source atom slot)).route triple color
  | .clause _ set, color =>
      X3CClauseOrthogonal.route set color

/-- Normalized local routes retain their exact typed endpoints. -/
theorem orientedIncidenceLocalRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (triple : Triple Variable) (color : WireColor) :
    (orientedIncidenceLocalRoute source triple color).head? =
        some (orientedTripleLocalPosition source triple) ∧
      (orientedIncidenceLocalRoute source triple color).getLast? =
        some (orientedIncidencePortPosition source triple color) := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      simpa [orientedIncidenceLocalRoute,
        orientedTripleLocalPosition,
        orientedIncidencePortPosition,
        LocalIncidenceDrawing.routeAt,
        LocalIncidenceDrawing.sourcePosition,
        LocalIncidenceDrawing.targetPosition] using
        (VariableOccurrence.orientedBoundaryDrawing_isValid
          variant (occurrencePolarity source atom slot)).1
            (localTriple, color)
  | fixedRed atom slot localTriple =>
      simpa [orientedIncidenceLocalRoute,
        orientedTripleLocalPosition,
        orientedIncidencePortPosition,
        LocalIncidenceDrawing.routeAt,
        LocalIncidenceDrawing.sourcePosition,
        LocalIncidenceDrawing.targetPosition] using
        (FixedRedConnector.boundaryDrawing_isValid
          (occurrencePolarity source atom slot)).1
            (localTriple, color)
  | clause clauseIndex set =>
      exact X3CClauseOrthogonal.drawing_isValid.1
        (set, color)

/-- Every normalized local route segment remains axis-aligned. -/
theorem orientedIncidenceLocalRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (triple : Triple Variable) (color : WireColor)
    (segment : GridSegment)
    (member :
      segment ∈ gridPolylineSegments
        (orientedIncidenceLocalRoute source triple color)) :
    segment.IsAxisAligned := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      exact
        (VariableOccurrence.orientedBoundaryDrawing_isValid
          variant (occurrencePolarity source atom slot)).2.1
            (localTriple, color) segment member
  | fixedRed atom slot localTriple =>
      exact
        (FixedRedConnector.boundaryDrawing_isValid
          (occurrencePolarity source atom slot)).2.1
            (localTriple, color) segment member
  | clause clauseIndex set =>
      exact X3CClauseOrthogonal.drawing_isValid.2.1
        (set, color) segment member

/-- Typed triple whose red continuation is incident to the current
occurrence's cycle-link element. -/
def slotContinuationTypedTriple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) : Triple Variable :=
  let polarity := occurrencePolarity source atom slot
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      .fixedRed atom slot
        (FixedRedConnector.slotContinuationTriple polarity)
  | .fixedGreen =>
      .ordinary atom slot .fixedGreen
        (VariableOccurrence.slotContinuationTriple polarity)
  | .fixedBlue =>
      .ordinary atom slot .fixedBlue
        (VariableOccurrence.slotContinuationTriple polarity)

/-- Typed triple whose red continuation is incident to the successor
cycle-link element. -/
def nextContinuationTypedTriple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) : Triple Variable :=
  let polarity := occurrencePolarity source atom slot
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      .fixedRed atom slot
        (FixedRedConnector.nextContinuationTriple polarity)
  | .fixedGreen =>
      .ordinary atom slot .fixedGreen
        (VariableOccurrence.nextContinuationTriple polarity)
  | .fixedBlue =>
      .ordinary atom slot .fixedBlue
        (VariableOccurrence.nextContinuationTriple polarity)

/-- Both standardized continuation triples are present in their occurrence
block. -/
theorem continuationTypedTriples_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    slotContinuationTypedTriple source atom slot ∈
        occurrenceTriples source atom slot ∧
      nextContinuationTypedTriple source atom slot ∈
        occurrenceTriples source atom slot := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases polarityEq : occurrencePolarity source atom slot <;>
    simp [slotContinuationTypedTriple, nextContinuationTypedTriple,
      kindEq, polarityEq, occurrenceTriples, allFixedRedTriples,
      allOrdinaryTriples, FixedRedConnector.slotContinuationTriple,
      FixedRedConnector.nextContinuationTriple,
      VariableOccurrence.slotContinuationTriple,
      VariableOccurrence.nextContinuationTriple]

/-- The first standardized continuation references the current cycle-link
element with zero offset. -/
theorem slotContinuationTypedTriple_red_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (tripleReferences source
      (slotContinuationTypedTriple source atom slot)).red =
        ⟨.cycleLink atom slot, (0, 0)⟩ := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases polarityEq : occurrencePolarity source atom slot <;>
    simp [slotContinuationTypedTriple, kindEq, polarityEq,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences, VariableOccurrence.slotContinuationTriple,
      FixedRedConnector.slotContinuationTriple,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement,
      firstCycleLinkSlot, secondCycleLinkSlot]

/-- The second standardized continuation references the successor
cycle-link element with zero offset. -/
theorem nextContinuationTypedTriple_red_reference
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (tripleReferences source
      (nextContinuationTypedTriple source atom slot)).red =
        ⟨.cycleLink atom (nextUsedSlot source atom slot), (0, 0)⟩ := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases polarityEq : occurrencePolarity source atom slot <;>
    simp [nextContinuationTypedTriple, kindEq, polarityEq,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences, VariableOccurrence.nextContinuationTriple,
      FixedRedConnector.nextContinuationTriple,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement,
      firstCycleLinkSlot, secondCycleLinkSlot]

/-- Standard current-slot boundary point for each connector template. -/
def slotCyclePortPosition (_ : VariableConnectorKind) : Cell :=
  (4, 0)

/-- Standard successor-slot boundary point for each connector template. -/
def nextCyclePortPosition (_ : VariableConnectorKind) : Cell :=
  (12, 0)

/-- The current-slot typed continuation ends at the standardized left cycle
port. -/
theorem orientedIncidencePortPosition_slotContinuation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    orientedIncidencePortPosition source
        (slotContinuationTypedTriple source atom slot) .red =
      slotCyclePortPosition
        (occurrenceConnectorKind source atom slot) := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases polarityEq : occurrencePolarity source atom slot <;>
    simp [orientedIncidencePortPosition,
      slotContinuationTypedTriple, slotCyclePortPosition,
      kindEq, polarityEq]

/-- The successor-slot continuation ends at the standardized right cycle
port. -/
theorem orientedIncidencePortPosition_nextContinuation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    orientedIncidencePortPosition source
        (nextContinuationTypedTriple source atom slot) .red =
      nextCyclePortPosition
        (occurrenceConnectorKind source atom slot) := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases polarityEq : occurrencePolarity source atom slot <;>
    simp [orientedIncidencePortPosition,
      nextContinuationTypedTriple, nextCyclePortPosition,
      kindEq, polarityEq]

/-- Local position of a red clause-core element in the rectilinear
template. -/
def redClauseElementLocalPosition {Variable : Type*} :
    RedElement Variable → Cell
  | .clauseInternal _ =>
      X3CClauseOrthogonal.elementPosition (.internal .left)
  | .clauseTerminal _ group =>
      X3CClauseOrthogonal.elementPosition
        (.terminal (terminalElementForColor .red group))
  | _ => (0, 0)

/-- Local position of a green clause-core element. -/
def greenClauseElementLocalPosition {Variable : Type*} :
    GreenElement Variable → Cell
  | .clauseInternal _ =>
      X3CClauseOrthogonal.elementPosition (.internal .right)
  | .clauseTerminal _ group =>
      X3CClauseOrthogonal.elementPosition
        (.terminal (terminalElementForColor .green group))
  | _ => (0, 0)

/-- Local position of a blue clause-core element. -/
def blueClauseElementLocalPosition {Variable : Type*} :
    BlueElement Variable → Cell
  | .clauseInternal _ =>
      X3CClauseOrthogonal.elementPosition (.internal .bottom)
  | .clauseTerminal _ group =>
      X3CClauseOrthogonal.elementPosition
        (.terminal (terminalElementForColor .blue group))
  | _ => (0, 0)

/-- The red port of a clause triple is exactly the position of its assembled
typed red element. -/
theorem incidencePortPosition_clause_red
    {Variable : Type*} (clauseIndex : Nat) (set : X3CClauseSet) :
    incidencePortPosition
        (Triple.clause (Variable := Variable) clauseIndex set) .red =
      redClauseElementLocalPosition
        (clauseTripleReferences
          (Variable := Variable) clauseIndex set).red.atom := by
  cases set <;>
    rfl

/-- The green port of a clause triple is exactly the position of its
assembled typed green element. -/
theorem incidencePortPosition_clause_green
    {Variable : Type*} (clauseIndex : Nat) (set : X3CClauseSet) :
    incidencePortPosition
        (Triple.clause (Variable := Variable) clauseIndex set) .green =
      greenClauseElementLocalPosition
        (clauseTripleReferences
          (Variable := Variable) clauseIndex set).green.atom := by
  cases set <;>
    rfl

/-- The blue port of a clause triple is exactly the position of its
assembled typed blue element. -/
theorem incidencePortPosition_clause_blue
    {Variable : Type*} (clauseIndex : Nat) (set : X3CClauseSet) :
    incidencePortPosition
        (Triple.clause (Variable := Variable) clauseIndex set) .blue =
      blueClauseElementLocalPosition
        (clauseTripleReferences
          (Variable := Variable) clauseIndex set).blue.atom := by
  cases set <;>
    rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
