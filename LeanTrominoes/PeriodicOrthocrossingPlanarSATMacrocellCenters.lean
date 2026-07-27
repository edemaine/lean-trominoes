import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellBounds
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Centers of planar-SAT macrocells

The non-carrier local drawings are indexed by points in the infinite
periodic lift of the constructed incidence drawing.  This file begins the
site-classification part of their separation proof by showing that a lifted
graph-vertex position uniquely determines both its protovertex and its
periodic translate.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Two points in the open fundamental square have unique periodic
translates in the infinite lift. -/
theorem translatedFundamentalPositions_eq
    (drawing : PeriodicGridDrawing)
    {first second firstTranslate secondTranslate : Cell}
    (firstBounds : drawing.PositionInFundamentalSquare first)
    (secondBounds : drawing.PositionInFundamentalSquare second)
    (equal :
      Cell.add first (drawing.periodTranslation firstTranslate) =
        Cell.add second (drawing.periodTranslation secondTranslate)) :
    first = second ∧ firstTranslate = secondTranslate := by
  have relativeEqual :
      first =
        Cell.add second
          (drawing.periodTranslation
            (Cell.sub secondTranslate firstTranslate)) := by
    rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
    rcases secondTranslate with
      ⟨secondTranslateX, secondTranslateY⟩
    simp only [Cell.add, Cell.sub,
      PeriodicGridDrawing.periodTranslation,
      Cell.scale, Prod.mk.injEq] at equal ⊢
    constructor
    · linear_combination equal.1
    · linear_combination equal.2
  have positionsEqual : first = second := by
    by_contra different
    exact
      PositionedPeriodicCNF.fundamentalPosition_ne_translated
        drawing firstBounds secondBounds different relativeEqual
  subst second
  have translationsEqual :
      drawing.periodTranslation firstTranslate =
        drawing.periodTranslation secondTranslate :=
    Cell.add_left_injective first equal
  have periodPositive :
      (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  refine ⟨rfl, ?_⟩
  rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
  rcases secondTranslate with
    ⟨secondTranslateX, secondTranslateY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Prod.mk.injEq] at translationsEqual
  apply Prod.ext
  · nlinarith [translationsEqual.1]
  · nlinarith [translationsEqual.2]

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

/-- The constructed drawing position of any declared protovertex lies in
the open fundamental square. -/
theorem drawing_vertexPosition_in_fundamental_square
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices) :
    (drawing graph).PositionInFundamentalSquare
      ((drawing graph).vertexPosition graph vertex) := by
  rw [drawing_vertexPosition_of_mem graph vertexMember]
  have indexLt :
      graph.vertices.idxOf vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare,
    vertexPosition, vertexX, drawing_gridSize, drawingGridSize]
  omega

/-- A lifted constructed-drawing vertex position uniquely determines both
the declared protovertex and its lattice translate. -/
theorem liftedDrawingVertexPosition_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {firstVertex secondVertex : Vertex}
    (firstVertexMember : firstVertex ∈ graph.vertices)
    (secondVertexMember : secondVertex ∈ graph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      Cell.add
          ((drawing graph).vertexPosition graph firstVertex)
          ((drawing graph).periodTranslation firstTranslate) =
        Cell.add
          ((drawing graph).vertexPosition graph secondVertex)
          ((drawing graph).periodTranslation secondTranslate)) :
    firstVertex = secondVertex ∧
      firstTranslate = secondTranslate := by
  have data :=
    (drawing graph).translatedFundamentalPositions_eq
      (drawing_vertexPosition_in_fundamental_square
        graph firstVertexMember)
      (drawing_vertexPosition_in_fundamental_square
        graph secondVertexMember)
      equal
  have indexEqual :
      graph.vertices.idxOf firstVertex =
        graph.vertices.idxOf secondVertex := by
    apply vertexPosition_injective
    simpa only [
      drawing_vertexPosition_of_mem graph firstVertexMember,
      drawing_vertexPosition_of_mem graph secondVertexMember] using
      data.1
  exact
    ⟨(List.idxOf_inj firstVertexMember).mp indexEqual,
      data.2⟩

/-- Every represented lifted clause site names a declared incidence-graph
clause vertex.  This also covers empty clauses, which have no incidence
edge witnessing their vertex. -/
theorem drawingClauseRouteSite_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : ClauseRouteSite}
    (siteMem : site ∈ drawingClauseRouteSites formula) :
    CNFVertex.clause site.1 ∈
      (PeriodicCNF.incidenceGraph formula).vertices := by
  rcases List.mem_flatMap.mp siteMem with
    ⟨taggedClause, taggedClauseMem, translateMem⟩
  rcases List.mem_map.mp translateMem with
    ⟨translate, translateMem, siteEqual⟩
  subst site
  apply List.mem_append_right
  simp only [PeriodicCNF.incidenceClauseVertices, List.mem_map]
  exact
    ⟨taggedClause.2,
      List.mem_range.mpr
        (List.snd_lt_of_mem_zipIdx taggedClauseMem),
      rfl⟩

/-- Every represented lifted variable site names a declared
incidence-graph variable vertex. -/
theorem drawingVariableRouteSite_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    CNFVertex.variable site.1 ∈
      (PeriodicCNF.incidenceGraph formula).vertices := by
  rw [drawingVariableRouteSites, List.mem_dedup] at siteMem
  rcases List.mem_map.mp siteMem with
    ⟨occurrence, occurrenceMem, siteEqual⟩
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem,
      translatedOccurrenceMem⟩
  rcases List.mem_map.mp translatedOccurrenceMem with
    ⟨translate, translateMem, occurrenceEqual⟩
  subst occurrence
  subst site
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      formula taggedIncidenceMem
  have endpoints :=
    (PeriodicCNF.incidenceGraph_isWellFormed formula).2
      taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  simpa only [CNFRouteOccurrence.variableOccurrence,
    CNFIncidence.edge_target] using endpoints.2

/-- Equal lifted positions of two represented clause sites force the
entire site keys to agree. -/
theorem liftedClauseRouteSite_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : ClauseRouteSite}
    (firstMem : first ∈ drawingClauseRouteSites formula)
    (secondMem : second ∈ drawingClauseRouteSites formula)
    (equal :
      liftedIncidenceVertexPosition formula
          (.clause first.1) first.2 =
        liftedIncidenceVertexPosition formula
          (.clause second.1) second.2) :
    first = second := by
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingClauseRouteSite_vertex_mem formula firstMem)
      (drawingClauseRouteSite_vertex_mem formula secondMem)
      equal
  have clauseIndexEqual : first.1 = second.1 := by
    exact CNFVertex.clause.inj data.1
  exact Prod.ext clauseIndexEqual data.2

/-- Equal lifted positions of two represented variable sites force the
entire site keys to agree. -/
theorem liftedVariableRouteSite_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : VariableRouteSite Variable}
    (firstMem : first ∈ drawingVariableRouteSites formula)
    (secondMem : second ∈ drawingVariableRouteSites formula)
    (equal :
      liftedIncidenceVertexPosition formula
          (.variable first.1) first.2 =
        liftedIncidenceVertexPosition formula
          (.variable second.1) second.2) :
    first = second := by
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingVariableRouteSite_vertex_mem formula firstMem)
      (drawingVariableRouteSite_vertex_mem formula secondMem)
      equal
  have variableEqual : first.1 = second.1 := by
    exact CNFVertex.variable.inj data.1
  exact Prod.ext variableEqual data.2

/-- A represented lifted clause site and represented lifted variable site
cannot occupy the same drawing-grid point. -/
theorem liftedClauseRouteSite_ne_liftedVariableRouteSite
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseSite : ClauseRouteSite}
    {variableSite : VariableRouteSite Variable}
    (clauseMem :
      clauseSite ∈ drawingClauseRouteSites formula)
    (variableMem :
      variableSite ∈ drawingVariableRouteSites formula) :
    liftedIncidenceVertexPosition formula
        (.clause clauseSite.1) clauseSite.2 ≠
      liftedIncidenceVertexPosition formula
        (.variable variableSite.1) variableSite.2 := by
  intro equal
  have data :=
    liftedDrawingVertexPosition_eq
      (PeriodicCNF.incidenceGraph formula)
      (drawingClauseRouteSite_vertex_mem formula clauseMem)
      (drawingVariableRouteSite_vertex_mem formula variableMem)
      equal
  cases data.1

end PeriodicOrthocrossing
end LeanTrominoes
