/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Canonical orthogonal incidence-route families

This file packages the pointwise endpoint and orthogonality obligations used
throughout the positioned reduction pipeline.  The package converts those
membership-style proofs into the whole-drawing `RoutesMatch` and
`IsOrthogonal` predicates, leaving vertex separation and planarity as
independent geometric obligations.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- One complete route per incidence, with canonical periodic endpoints and
pointwise orthogonality. -/
structure CanonicalOrthogonalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) where
  routes : IncidenceRoutes
  endpoints :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        (routes clauseIndex literalIndex).head? =
            some (canonicalClausePosition placement clause) ∧
          (routes clauseIndex literalIndex).getLast? =
            some
              (canonicalLiteralPosition
                placement clause literal)
  orthogonal :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        PeriodicOrthocrossing.OrthogonalPolyline
          (routes clauseIndex literalIndex)

namespace CanonicalOrthogonalIncidenceRoutes

/-- The pointwise endpoint fields in metadata-rich incidence form. -/
theorem endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (family.routes
        tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (incidenceVertexPositionAt source placement
            (.clause tagged.1.clauseIndex)) ∧
      (family.routes
        tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            (placement.position tagged.1.literal.atom)
            (placement.translation tagged.1.edge.offset)) := by
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember, taggedEqual⟩
  have endpoints :=
    family.endpoints
      clause tagged.1.clauseIndex clauseMember
      literal tagged.1.literalIndex literalMember
  have clauseIndexLt :
      tagged.1.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseLookup :
      source.clauses[tagged.1.clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  rw [taggedEqual]
  constructor
  · simpa [incidenceVertexPositionAt,
      List.getElem?_eq_getElem clauseIndexLt, clauseLookup]
      using endpoints.1
  · simpa [canonicalLiteralPosition, CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using endpoints.2

/-- Canonical pointwise endpoints imply the graph-level route compatibility
predicate once the physical period is positive. -/
theorem routesMatch
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement)
    (periodPositive : 0 < placement.period) :
    (incidenceDrawing source placement family.routes).RoutesMatch
      source.erase.incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges source.erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedIncidenceEqual⟩
  have endpoints :=
    family.endpoints_of_tagged taggedIncidenceMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source.erase
  have edgeMember :
      taggedIncidence.1.edge ∈ source.erase.incidenceGraph.edges :=
    List.fst_mem_of_mem_zipIdx
      (PeriodicCNF.tagged_incidence_edge_mem
        source.erase taggedIncidenceMember)
  have endpointMembers :=
    graphWellFormed.2 taggedIncidence.1.edge edgeMember
  have sourcePosition :=
    incidenceDrawing_vertexPosition_of_mem
      source placement family.routes endpointMembers.1
  have targetPosition :=
    incidenceDrawing_vertexPosition_of_mem
      source placement family.routes endpointMembers.2
  have routeLookup :=
    incidenceDrawing_edgeRoute_of_tagged
      source placement family.routes taggedIncidenceMember
  rw [← taggedIncidenceEqual]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition, CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition, CNFIncidence.edge_target]
    simp only [incidenceVertexPositionAt,
      PeriodicGridDrawing.periodTranslation]
    rw [incidenceDrawing_gridSize
      source placement family.routes periodPositive]
    simpa [PeriodicVariablePlacement.translation] using
      endpoints.2

/-- Pointwise polyline orthogonality implies orthogonality of the assembled
periodic incidence drawing. -/
theorem isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement) :
    (incidenceDrawing source placement family.routes).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  change route ∈
    incidenceEdgeRoutes source family.routes at routeMember
  rw [incidenceEdgeRoutes_eq_metadata_map] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  subst route
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember, _⟩
  exact family.orthogonal
    clause incidence.clauseIndex clauseMember
    literal incidence.literalIndex literalMember

end CanonicalOrthogonalIncidenceRoutes
end PositionedPeriodicCNF
end LeanTrominoes
