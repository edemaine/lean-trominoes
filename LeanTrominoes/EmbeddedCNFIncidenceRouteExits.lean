import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.OrthogonalPolylineHeadReplacement

/-!
# First exits of certified finite incidence routes

Every genuine route of a valid finite embedded-CNF drawing connects a clause
vertex to a variable vertex.  The drawing's duplicate-free vertex-position
list makes those endpoints distinct, so the route necessarily contains a
second listed point.  This file exposes that point without inspecting any
particular gadget's coordinate table.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- In a planar embedded drawing, the clause and variable endpoints of every
genuine incidence occupy distinct cells. -/
theorem EmbeddedCNFIncidenceDrawing.incidenceEndpoints_ne_of_planar
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    clause.position ≠ drawing.variablePosition literal.1 := by
  have atomMember :
      literal.1 ∈ drawing.variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      List.mem_dedup]
    apply List.mem_flatMap.mpr
    refine
      ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, ?_⟩
    exact List.mem_map.mpr
      ⟨literal,
        List.fst_mem_of_mem_zipIdx literalMember,
        rfl⟩
  have variablePositionMember :
      drawing.variablePosition literal.1 ∈
        drawing.variableVertices.map drawing.variablePosition :=
    List.mem_map.mpr
      ⟨literal.1, atomMember, rfl⟩
  have clausePositionMember :
      clause.position ∈
        drawing.formula.map EmbeddedClause.position :=
    List.mem_map.mpr
      ⟨clause,
        List.fst_mem_of_mem_zipIdx clauseMember,
        rfl⟩
  have positionsNodup :
      (drawing.variableVertices.map drawing.variablePosition ++
        drawing.formula.map EmbeddedClause.position).Nodup := by
    simpa [EmbeddedCNFIncidenceDrawing.vertexPositions] using
      planar.2.2.2
  have halvesDifferent :=
    (List.nodup_append.mp positionsNodup).2.2
  intro endpointsEqual
  exact
    halvesDifferent
      (drawing.variablePosition literal.1)
      variablePositionMember
      clause.position clausePositionMember
      endpointsEqual.symm

/-- Every genuine route in a valid finite drawing has a first exit after its
clause endpoint. -/
theorem EmbeddedCNFIncidenceDrawing.exists_route_tail_head?_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (valid : drawing.IsValid)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (drawing.routes clauseIndex literalIndex).tail.head? =
        some exit := by
  have endpoints :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      drawing valid.1
      clause clauseIndex clauseMember
      literal literalIndex literalMember
  exact List.exists_tail_head?_of_endpoints_ne
    endpoints.1 endpoints.2
    (drawing.incidenceEndpoints_ne_of_planar
      valid.2.2 clauseMember literalMember)

end PlanarThreeSAT
end LeanTrominoes
