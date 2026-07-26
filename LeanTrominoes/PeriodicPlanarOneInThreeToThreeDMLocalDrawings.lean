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
