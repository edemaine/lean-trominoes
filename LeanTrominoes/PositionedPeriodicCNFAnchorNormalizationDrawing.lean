/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization

/-!
# Drawing invariance under clause-anchor normalization

Anchor normalization changes the syntactic literal offsets but not the
periodic incidence graph: the graph construction was already subtracting
the same first-literal anchor.  Moving the displayed clause point to its
canonical position likewise leaves the stored vertex position unchanged.

Consequently the complete `PeriodicGridDrawing` is definitionally the same
after list algebra, and every certified planar incidence presentation
transports to the normalized formula without rebuilding or rechecking a
single route.
-/

namespace LeanTrominoes

namespace PeriodicClause

/-- Anchor normalization changes no literal atoms or their order. -/
@[simp]
theorem anchorNormalize_map_atom
    {Variable : Type*} (clause : PeriodicClause Variable) :
    clause.anchorNormalize.map PeriodicLiteral.atom =
      clause.map PeriodicLiteral.atom := by
  simp [anchorNormalize, List.map_map, Function.comp_def]

end PeriodicClause

namespace PeriodicCNF

/-- Anchor normalization changes no variable occurrences or their order. -/
@[simp]
theorem variableOccurrences_anchorNormalize
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    formula.anchorNormalize.variableOccurrences =
      formula.variableOccurrences := by
  simp [PeriodicCNF.anchorNormalize, variableOccurrences,
    List.flatMap_map]

/-- One normalized literal produces exactly the same incidence protoedge as
the original literal. -/
theorem incidenceEdge_anchorNormalize
    {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    incidenceEdge clauseIndex
        (clauseAnchor clause.anchorNormalize)
        (literal.anchorNormalize (clauseAnchor clause)) =
      incidenceEdge clauseIndex (clauseAnchor clause) literal := by
  unfold incidenceEdge
  simp only [PeriodicClause.clauseAnchor_anchorNormalize,
    PeriodicLiteral.anchorNormalize_atom,
    PeriodicLiteral.anchorNormalize_offset]
  congr 1
  rcases literal.offset with ⟨literalX, literalY⟩
  rcases clauseAnchor clause with ⟨anchorX, anchorY⟩
  apply Prod.ext <;> simp [Cell.sub]

/-- The incidence edges of one clause are unchanged by normalization. -/
theorem clauseIncidenceEdges_anchorNormalize
    {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    clauseIncidenceEdges clauseIndex clause.anchorNormalize =
      clauseIncidenceEdges clauseIndex clause := by
  unfold clauseIncidenceEdges PeriodicClause.anchorNormalize
  rw [List.map_map]
  apply List.map_congr_left
  intro literal literalMember
  exact incidenceEdge_anchorNormalize clauseIndex clause literal

/-- The complete finite incidence graph is unchanged by independently
normalizing every clause orbit. -/
theorem incidenceGraph_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    incidenceGraph formula.anchorNormalize =
      incidenceGraph formula := by
  apply PeriodicGraph.equivData.injective
  apply Prod.ext
  · change
      incidenceVariableVertices formula.anchorNormalize ++
          incidenceClauseVertices formula.anchorNormalize =
        incidenceVariableVertices formula ++
          incidenceClauseVertices formula
    rw [show incidenceVariableVertices formula.anchorNormalize =
        incidenceVariableVertices formula by
      simp [incidenceVariableVertices]]
    congr 1
    simp [incidenceClauseVertices, PeriodicCNF.anchorNormalize]
  · simp only [PeriodicGraph.equivData, incidenceGraph,
      PeriodicCNF.anchorNormalize]
    rw [List.zipIdx_map]
    simp only [List.flatMap_map, Prod.map, id_eq]
    apply List.flatMap_congr
    intro taggedClause taggedClauseMember
    rcases taggedClause with ⟨clause, clauseIndex⟩
    exact clauseIncidenceEdges_anchorNormalize
      clauseIndex clause

end PeriodicCNF

namespace PositionedPeriodicCNF

/-- The positioned clause list has unchanged length after normalization. -/
@[simp]
theorem anchorNormalize_clauses_length
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (source.anchorNormalize placement).clauses.length =
      source.clauses.length := by
  simp [anchorNormalize]

/-- The canonical position of a normalized clause is its already normalized
displayed position. -/
theorem canonicalClausePosition_anchorNormalize
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) :
    canonicalClausePosition placement
        ⟨canonicalClausePosition placement clause,
          clause.literals.anchorNormalize⟩ =
      canonicalClausePosition placement clause := by
  unfold canonicalClausePosition
  simp only [PeriodicClause.clauseAnchor_anchorNormalize]
  rcases canonicalClausePosition placement clause with
    ⟨positionX, positionY⟩
  simp [PeriodicVariablePlacement.translation,
    Cell.scale, Cell.sub]

/-- The stored incidence-graph vertex positions are unchanged by anchor
normalization. -/
theorem incidenceVertexPositions_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    incidenceVertexPositions
        (source.anchorNormalize placement) placement =
      incidenceVertexPositions source placement := by
  unfold incidenceVertexPositions
  rw [erase_anchorNormalize]
  congr 1
  · simp [PeriodicCNF.incidenceVariableVertices]
  · simp [anchorNormalize,
      canonicalClausePosition_anchorNormalize]

/-- The flattened route list is unchanged because normalization preserves
every clause and literal list length and all clause/literal indices. -/
theorem incidenceEdgeRoutes_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) :
    incidenceEdgeRoutes
        (source.anchorNormalize placement) routes =
      incidenceEdgeRoutes source routes := by
  unfold incidenceEdgeRoutes
    PositionedPeriodicCNF.anchorNormalize
  rw [List.zipIdx_map]
  simp only [List.flatMap_map, Prod.map, id_eq]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp only [PeriodicClause.anchorNormalize,
    List.zipIdx_map, List.map_map, Prod.map, id_eq,
    Function.comp_def]

/-- The complete finite drawing data is unchanged by anchor normalization. -/
theorem incidenceDrawing_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) :
    incidenceDrawing
        (source.anchorNormalize placement) placement routes =
      incidenceDrawing source placement routes := by
  apply PeriodicGridDrawing.equivData.injective
  simp [PeriodicGridDrawing.equivData,
    incidenceDrawing,
    incidenceVertexPositions_anchorNormalize,
    incidenceEdgeRoutes_anchorNormalize]

/-- A certified positioned planar incidence drawing transports unchanged to
the anchor-normalized formula. -/
def PlanarIncidencePresentation.anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement) :
    PlanarIncidencePresentation
      (source.anchorNormalize placement) placement where
  routes := presentation.routes
  periodPositive := presentation.periodPositive
  compatible := by
    rw [incidenceDrawing_anchorNormalize,
      erase_anchorNormalize,
      PeriodicCNF.incidenceGraph_anchorNormalize]
    exact presentation.compatible
  orthogonal := by
    rw [incidenceDrawing_anchorNormalize]
    exact presentation.orthogonal
  planar := by
    rw [incidenceDrawing_anchorNormalize]
    exact presentation.planar

end PositionedPeriodicCNF

end LeanTrominoes
