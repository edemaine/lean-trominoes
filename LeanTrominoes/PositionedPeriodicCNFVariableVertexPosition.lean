import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing

/-!
# Variable-prefix vertex positions

A named version of the variable-vertex position map used at the front of a
positioned periodic CNF incidence drawing.  Naming this function lets
separate modules share the map definition without forcing Lean to compare
distinct generated helpers for identical inline pattern matches.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Position map on the variable-only prefix of the incidence vertex list. -/
def incidenceVariableVertexPosition
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable) :
    CNFVertex Variable → Cell
  | .variable atom => placement.position atom
  | .clause _ => (0, 0)

/-- Expose the incidence position list using the shared named variable-prefix
map. -/
theorem incidenceVertexPositions_eq_variablePrefix_append
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    source.incidenceVertexPositions placement =
      source.erase.incidenceVariableVertices.map
          (incidenceVariableVertexPosition placement) ++
        source.clauses.map (canonicalClausePosition placement) := by
  rfl

end PositionedPeriodicCNF
end LeanTrominoes
