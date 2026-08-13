/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-!
# Canonical route families from planar presentations

The pointwise canonical-route interface is convenient for local route
transformations, while an existing planar presentation stores its endpoint
and orthogonality proofs at the assembled-drawing level.  This file supplies
the lossless adapter between those two views.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A genuine positioned clause/literal pair determines a tagged entry in
the flattened incidence metadata list. -/
theorem exists_taggedIncidence_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ incidenceIndex,
      (CNFIncidence.mk clauseIndex clause.literals literalIndex literal,
          incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
  let incidence : CNFIncidence Variable :=
    ⟨clauseIndex, clause.literals, literalIndex, literal⟩
  have incidenceMember :
      incidence ∈ PeriodicCNF.incidencesWithMetadata source.erase := by
    rw [PeriodicCNF.mem_incidencesWithMetadata_iff]
    constructor
    · change
        (clause.literals, clauseIndex) ∈
          (source.clauses.map PositionedPeriodicClause.literals).zipIdx
      rw [List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(clause, clauseIndex), clauseMember, rfl⟩
    · exact literalMember
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  refine ⟨incidenceIndex, ?_⟩
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
  exact ⟨incidenceIndexLt, incidenceAt⟩

/-- Forgetting the assembled-drawing packaging of a planar presentation
yields the same routes with pointwise canonical endpoints and
orthogonality. -/
def PlanarIncidencePresentation.canonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) :
    CanonicalOrthogonalIncidenceRoutes source placement where
  routes := presentation.routes
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rcases exists_taggedIncidence_of_members source clauseMember literalMember with
      ⟨incidenceIndex, taggedMember⟩
    have endpoints := presentation.route_endpoints_of_tagged taggedMember
    have clauseIndexLt : clauseIndex < source.clauses.length :=
      List.snd_lt_of_mem_zipIdx clauseMember
    have clauseAt : source.clauses[clauseIndex] = clause :=
      (List.mem_zipIdx' clauseMember).2.symm
    change
      (presentation.routes clauseIndex literalIndex).head? = _ ∧
        (presentation.routes clauseIndex literalIndex).getLast? = _
      at endpoints
    rw [incidenceVertexPositionAt_clause source placement clauseIndex
      clauseIndexLt, clauseAt] at endpoints
    simpa [canonicalLiteralPosition, CNFIncidence.edge,
      PeriodicCNF.incidenceEdge,
      PeriodicGridDrawing.periodTranslation,
      incidenceDrawing_gridSize source placement presentation.routes
        presentation.periodPositive,
      PeriodicVariablePlacement.translation] using endpoints
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rcases exists_taggedIncidence_of_members source clauseMember literalMember with
      ⟨incidenceIndex, taggedMember⟩
    exact presentation.route_orthogonal_of_tagged taggedMember

namespace CanonicalOrthogonalIncidenceRoutes

/-- Unit subdivision preserves a canonical route family's endpoints and
orthogonality pointwise. -/
def unitSubdivide
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (family : CanonicalOrthogonalIncidenceRoutes source placement) :
    CanonicalOrthogonalIncidenceRoutes source placement where
  routes := fun clauseIndex literalIndex =>
    AxisDirection.unitSubdividePolyline
      (family.routes clauseIndex literalIndex)
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have endpoints := family.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
    have orthogonal := family.orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember
    have routeNonempty : family.routes clauseIndex literalIndex ≠ [] := by
      intro routeEq
      rw [routeEq] at endpoints
      simp at endpoints
    constructor
    · rw [AxisDirection.unitSubdividePolyline_head? routeNonempty]
      exact endpoints.1
    · rw [AxisDirection.unitSubdividePolyline_getLast?
        routeNonempty orthogonal]
      exact endpoints.2
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact AxisDirection.unitSubdividePolyline_orthogonal
      (family.orthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember)

end CanonicalOrthogonalIncidenceRoutes

end PositionedPeriodicCNF
end LeanTrominoes
