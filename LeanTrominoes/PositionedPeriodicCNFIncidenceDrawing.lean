import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicGridDrawing

/-!
# Planar incidence certificates for positioned periodic CNF formulas

This file gives the geometric interface shared by the remaining reduction
layers.  A positioned periodic formula supplies clause vertices, a
`PeriodicVariablePlacement` supplies variable vertices and the physical
period, and an incidence-route family supplies one polyline per literal in
presentation order.

The incidence graph normalizes every clause orbit to the first literal's
offset.  Accordingly the canonical clause protovariable position subtracts
that anchor translation from the displayed clause occurrence.  At the
anchor translate, the lifted clause is therefore exactly at its displayed
position and each edge target is exactly the corresponding literal
occurrence position.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- One route for every `(clause index, literal index)` pair.  Values outside
the finite presentation are harmless because `edgeRoutes` enumerates only
genuine incidences. -/
abbrev IncidenceRoutes := Nat → Nat → List Cell

/-- Canonical position of a clause protovariable after subtracting the
incidence graph's common clause anchor. -/
def canonicalClausePosition {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) : Cell :=
  Cell.sub clause.position
    (placement.translation
      (PeriodicCNF.clauseAnchor clause.literals))

/-- Vertex positions in exactly the variable-then-clause order used by
`PeriodicCNF.incidenceGraph`. -/
def incidenceVertexPositions {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    List Cell :=
  (source.erase.incidenceVariableVertices.map fun vertex =>
    match vertex with
    | .variable atom => placement.position atom
    | .clause _ => (0, 0)) ++
  source.clauses.map (canonicalClausePosition placement)

/-- Incidence routes in exactly the clause-major, literal-minor order used
by `PeriodicCNF.incidenceGraph`. -/
def incidenceEdgeRoutes {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : List (List Cell) :=
  source.clauses.zipIdx.flatMap fun taggedClause =>
    taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      routes taggedClause.2 taggedLiteral.2

/-- The finite periodic drawing assembled from positioned vertices and one
route per literal occurrence. -/
def incidenceDrawing {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : PeriodicGridDrawing where
  gridSizePred := Nat.pred placement.period
  vertexPositions := incidenceVertexPositions source placement
  edgeRoutes := incidenceEdgeRoutes source routes

/-- A positioned periodic formula has a certified planar orthogonal
incidence drawing with the declared variable positions and route family. -/
structure PlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) where
  routes : IncidenceRoutes
  periodPositive : 0 < placement.period
  compatible :
    (incidenceDrawing source placement routes).IsCompatible
      source.erase.incidenceGraph
  orthogonal :
    (incidenceDrawing source placement routes).IsOrthogonal
  planar :
    (incidenceDrawing source placement routes).IsPlanar

@[simp]
theorem incidenceDrawing_gridSize {Variable : Type*}
    [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period) :
    (incidenceDrawing source placement routes).gridSize =
      placement.period := by
  simp [incidenceDrawing, PeriodicGridDrawing.gridSize, Nat.pred_eq_sub_one]
  omega

@[simp]
theorem incidenceVertexPositions_length {Variable : Type*}
    [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (incidenceVertexPositions source placement).length =
      source.erase.incidenceGraph.vertices.length := by
  simp [incidenceVertexPositions, PeriodicCNF.incidenceGraph,
    PositionedPeriodicCNF.erase,
    PeriodicCNF.incidenceClauseVertices]

@[simp]
theorem incidenceEdgeRoutes_length {Variable : Type*}
    [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    (incidenceEdgeRoutes source routes).length =
      source.erase.incidenceGraph.edges.length := by
  unfold incidenceEdgeRoutes PeriodicCNF.incidenceGraph
    PositionedPeriodicCNF.erase
  rw [List.zipIdx_map]
  simp [PeriodicCNF.clauseIncidenceEdges,
    Function.comp_def, Prod.map]

/-- At its logical anchor translate, a canonical clause protovariable lifts
back to the displayed positioned clause vertex. -/
@[simp]
theorem canonicalClausePosition_at_anchor {Variable : Type*}
    (_source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) :
    Cell.add (canonicalClausePosition placement clause)
        (placement.translation
          (PeriodicCNF.clauseAnchor clause.literals)) =
      clause.position := by
  simp [canonicalClausePosition,
    PeriodicVariablePlacement.translation, Cell.add, Cell.sub]

/-- The target of an incidence edge lifted at its clause anchor is the
physical occurrence position of that edge's literal. -/
theorem incidence_target_at_anchor {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    Cell.add
        (placement.position literal.atom)
        (placement.translation
          (Cell.add (PeriodicCNF.clauseAnchor clause)
            (PeriodicCNF.incidenceEdge clauseIndex
              (PeriodicCNF.clauseAnchor clause) literal).offset)) =
      placement.literalPosition literal := by
  simp [PeriodicCNF.incidenceEdge,
    PeriodicVariablePlacement.literalPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub]

end PositionedPeriodicCNF
end LeanTrominoes
