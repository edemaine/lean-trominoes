import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes
import LeanTrominoes.PositionedPeriodicCNFScaling
import LeanTrominoes.RetainedRayRasterization

/-!
# Rasterizing canonical retained-ray incidence routes

A retained-ray certificate says that every segment of a positioned periodic
CNF incidence route has one of the eleven slopes supported by the planar-SAT
construction.  This file packages the pointwise endpoint and retained-ray
conditions together, then turns them into an ordinary canonical orthogonal
route family after positive uniform scaling and staircase rasterization.

The logical formula is unchanged by coordinate scaling.  Exact endpoint
preservation therefore makes the rasterized family immediately compatible
with the scaled positioned source and variable placement.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PeriodicEightOccurrenceSplit

/-- One complete route per incidence, with canonical periodic endpoints and
retained-ray geometry. -/
structure CanonicalRetainedRayIncidenceRoutes
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
  retained :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        RetainedRayPolyline
          (routes clauseIndex literalIndex)

namespace CanonicalRetainedRayIncidenceRoutes

/-- Whole-drawing route compatibility recovers the pointwise canonical
endpoint equations for any genuine positioned incidence. -/
theorem canonicalEndpoints_of_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (routesMatch :
      (incidenceDrawing source placement routes).RoutesMatch
        source.erase.incidenceGraph)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (routes clauseIndex literalIndex).head? =
        some (canonicalClausePosition placement clause) ∧
      (routes clauseIndex literalIndex).getLast? =
        some (canonicalLiteralPosition placement clause literal) := by
  let incidence : CNFIncidence Variable :=
    ⟨clauseIndex, clause.literals, literalIndex, literal⟩
  have incidenceMember :
      incidence ∈
        PeriodicCNF.incidencesWithMetadata source.erase := by
    rw [PeriodicCNF.mem_incidencesWithMetadata_iff]
    constructor
    · change
        (clause.literals, clauseIndex) ∈
          (source.clauses.map
            PositionedPeriodicClause.literals).zipIdx
      rw [List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(clause, clauseIndex), clauseMember, rfl⟩
    · exact literalMember
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have taggedMember :
      (incidence, (incidenceIndex : Nat)) ∈
        (PeriodicCNF.incidencesWithMetadata
          source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndex.isLt, incidenceEqual⟩
  have taggedEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source.erase
  have endpointMembers :=
    graphWellFormed.2 incidence.edge
      (List.fst_mem_of_mem_zipIdx taggedEdgeMember)
  have sourcePosition :=
    incidenceDrawing_vertexPosition_of_mem
      source placement routes endpointMembers.1
  have targetPosition :=
    incidenceDrawing_vertexPosition_of_mem
      source placement routes endpointMembers.2
  have routeLookup :=
    incidenceDrawing_edgeRoute_of_tagged
      source placement routes taggedMember
  have endpoints :=
    routesMatch (incidence.edge, (incidenceIndex : Nat))
      taggedEdgeMember
  rw [routeLookup] at endpoints
  rw [sourcePosition, targetPosition] at endpoints
  have clauseIndexLt :
      clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseLookup :
      source.clauses[clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  simpa [incidence, incidenceVertexPositionAt,
    List.getElem?_eq_getElem clauseIndexLt,
    clauseLookup,
    PeriodicGridDrawing.periodTranslation,
    incidenceDrawing_gridSize
      source placement routes periodPositive,
    canonicalLiteralPosition,
    PeriodicVariablePlacement.translation,
    CNFIncidence.edge,
    PeriodicCNF.incidenceEdge] using endpoints

/-- Canonical lifted literal endpoints scale uniformly. -/
@[simp]
theorem canonicalLiteralPosition_scale
    {Variable : Type*}
    (factor : Nat)
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    canonicalLiteralPosition
        (placement.scale factor) (clause.scale factor) literal =
      Cell.scale factor
        (canonicalLiteralPosition placement clause literal) := by
  simp [canonicalLiteralPosition, Cell.scale_add]

/-- Positive uniform scaling followed by retained-ray rasterization produces
canonical orthogonal routes with the same scaled endpoints. -/
def rasterize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {factor : Nat} (factorPositive : 0 < factor)
    (family :
      CanonicalRetainedRayIncidenceRoutes source placement) :
    CanonicalOrthogonalIncidenceRoutes
      (source.scale factor) (placement.scale factor) where
  routes :=
    rasterizeRetainedIncidenceRoutes factor family.routes
  endpoints := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    rw [scale_clauses, List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual :
        taggedClause.2 = clauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst clauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (literal, literalIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using literalMember
    have sourceEndpoints :=
      family.endpoints
        taggedClause.1 taggedClause.2 taggedClauseMember
        literal literalIndex sourceLiteralMember
    constructor
    · simpa using
        rasterizeRetainedIncidenceRoutes_head?
          factor family.routes taggedClause.2 literalIndex
          sourceEndpoints.1
    · simpa using
        rasterizeRetainedIncidenceRoutes_getLast?
          factor family.routes taggedClause.2 literalIndex
          sourceEndpoints.2
  orthogonal := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    rw [scale_clauses, List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual :
        taggedClause.2 = clauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst clauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (literal, literalIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using literalMember
    exact
      rasterizeRetainedIncidenceRoutes_orthogonal
        factorPositive family.routes taggedClause.2 literalIndex
        (family.retained
          taggedClause.1 taggedClause.2 taggedClauseMember
          literal literalIndex sourceLiteralMember)

end CanonicalRetainedRayIncidenceRoutes
end PositionedPeriodicCNF
end LeanTrominoes
