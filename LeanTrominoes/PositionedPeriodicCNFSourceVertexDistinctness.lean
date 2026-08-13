/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup

/-!
# Distinct positioned clause and variable vertices

Compatibility makes the finite incidence drawing injective on its listed
graph vertices.  In particular, a genuine positioned clause vertex cannot
coincide with the base position of the variable targeted by any genuine
literal incidence, even when the two incidences belong to different clauses.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A genuine clause's canonical base position differs from the base
variable position underlying every genuine literal incidence. -/
theorem canonicalClausePosition_ne_variablePosition_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (compatible :
      (incidenceDrawing source placement routes).IsCompatible
        source.erase.incidenceGraph)
    {firstClause secondClause :
      PositionedPeriodicClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        source.clauses.zipIdx)
    {firstLiteral : PeriodicLiteral Variable}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        source.clauses.zipIdx)
    {secondLiteral : PeriodicLiteral Variable}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    canonicalClausePosition placement firstClause ≠
      placement.position secondLiteral.atom := by
  rcases
      exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        firstClauseMember firstLiteralMember with
    ⟨_firstRouteIndex, firstIncidenceMember,
      _firstRouteMember⟩
  rcases
      exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        secondClauseMember secondLiteralMember with
    ⟨_secondRouteIndex, secondIncidenceMember,
      _secondRouteMember⟩
  have firstEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase firstIncidenceMember
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondIncidenceMember
  have firstEndpointMembers :=
    compatible.1.2
      (⟨firstClauseIndex, firstClause.literals,
        firstLiteralIndex, firstLiteral⟩ :
        CNFIncidence Variable).edge
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
  have secondEndpointMembers :=
    compatible.1.2
      (⟨secondClauseIndex, secondClause.literals,
        secondLiteralIndex, secondLiteral⟩ :
        CNFIncidence Variable).edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have firstSourceMember :
      CNFVertex.clause firstClauseIndex ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using
      firstEndpointMembers.1
  have secondTargetMember :
      CNFVertex.variable secondLiteral.atom ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using
      secondEndpointMembers.2
  have firstLookup :
      (incidenceDrawing source placement routes).vertexPosition
          source.erase.incidenceGraph
          (.clause firstClauseIndex) =
        canonicalClausePosition placement firstClause := by
    rw [incidenceDrawing_vertexPosition_of_mem
      source placement routes firstSourceMember]
    simp [incidenceVertexPositionAt,
      (List.mem_zipIdx_iff_getElem?).mp firstClauseMember]
  have secondLookup :
      (incidenceDrawing source placement routes).vertexPosition
          source.erase.incidenceGraph
          (.variable secondLiteral.atom) =
        placement.position secondLiteral.atom := by
    rw [incidenceDrawing_vertexPosition_of_mem
      source placement routes secondTargetMember]
    rfl
  intro positionsEqual
  have verticesEqual :=
    incidenceDrawing_vertexPosition_injective_on_of_compatible
      source placement routes compatible
      firstSourceMember secondTargetMember
      (firstLookup.trans
        (positionsEqual.trans secondLookup.symm))
  cases verticesEqual

end PositionedPeriodicCNF
end LeanTrominoes
