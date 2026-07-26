import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Canonical orthogonal incidence routes

Endpoint compatibility and orthogonality do not themselves require
planarity.  This file gives every positioned periodic CNF a total canonical
route family satisfying those two obligations.

Each route uses fresh horizontal and vertical detour coordinates strictly
larger than both endpoint coordinates.  Consequently all four segments are
nondegenerate and axis-aligned, even if the two advertised endpoints happen
to coincide.  Later geometric constructions may replace these deliberately
generic detours by noncrossing lanes while reusing the endpoint interface.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- An integer coordinate strictly beyond two given coordinates. -/
def freshDetourCoordinate (first second : Int) : Int :=
  max first second + 1

theorem lt_freshDetourCoordinate_left (first second : Int) :
    first < freshDetourCoordinate first second := by
  unfold freshDetourCoordinate
  omega

theorem lt_freshDetourCoordinate_right (first second : Int) :
    second < freshDetourCoordinate first second := by
  unfold freshDetourCoordinate
  omega

/-- A four-segment Manhattan detour with exact advertised endpoints. -/
def orthogonalDetour (source target : Cell) : List Cell :=
  let detourX := freshDetourCoordinate source.1 target.1
  let detourY := freshDetourCoordinate source.2 target.2
  [source,
    (detourX, source.2),
    (detourX, detourY),
    (target.1, detourY),
    target]

@[simp]
theorem orthogonalDetour_head? (source target : Cell) :
    (orthogonalDetour source target).head? = some source := by
  rfl

@[simp]
theorem orthogonalDetour_getLast? (source target : Cell) :
    (orthogonalDetour source target).getLast? = some target := by
  rfl

/-- Every canonical detour is an orthogonal polyline. -/
theorem orthogonalDetour_orthogonal (source target : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (orthogonalDetour source target) := by
  rcases source with ⟨sourceX, sourceY⟩
  rcases target with ⟨targetX, targetY⟩
  simp only [orthogonalDetour,
    PeriodicOrthocrossing.OrthogonalPolyline,
    List.isChain_cons_cons, List.isChain_singleton]
  constructor
  · left
    exact
      ⟨rfl, ne_of_lt
        (lt_freshDetourCoordinate_left sourceX targetX)⟩
  constructor
  · right
    exact
      ⟨rfl, ne_of_lt
        (lt_freshDetourCoordinate_left sourceY targetY)⟩
  constructor
  · left
    exact
      ⟨rfl, ne_of_gt
        (lt_freshDetourCoordinate_right sourceX targetX)⟩
  constructor
  · right
    exact
      ⟨rfl, ne_of_gt
        (lt_freshDetourCoordinate_right sourceY targetY)⟩
  · trivial

/-- Canonical lifted target of one literal from its clause's normalized
anchor translate. -/
def canonicalLiteralPosition
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) : Cell :=
  Cell.add
    (placement.position literal.atom)
    (placement.translation
      (Cell.sub literal.offset
        (PeriodicCNF.clauseAnchor clause.literals)))

/-- Total family of canonical orthogonal incidence detours. -/
def orthogonalIncidenceRoutes
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            orthogonalDetour
              (canonicalClausePosition placement clause)
              (canonicalLiteralPosition placement clause literal)

/-- A genuine clause/literal pair retrieves its canonical detour. -/
theorem orthogonalIncidenceRoutes_of_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    orthogonalIncidenceRoutes source placement
        clauseIndex literalIndex =
      orthogonalDetour
        (canonicalClausePosition placement clause)
        (canonicalLiteralPosition placement clause literal) := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [orthogonalIncidenceRoutes, clauseLookup, literalLookup]

/-- Every metadata-rich incidence has exact canonical endpoints. -/
theorem orthogonalIncidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (orthogonalIncidenceRoutes source placement
        tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (incidenceVertexPositionAt source placement
            (.clause tagged.1.clauseIndex)) ∧
      (orthogonalIncidenceRoutes source placement
        tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            (placement.position tagged.1.literal.atom)
            (placement.translation tagged.1.edge.offset)) := by
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember, taggedEqual⟩
  have clauseIndexLt :
      tagged.1.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseLookup :
      source.clauses[tagged.1.clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  rw [orthogonalIncidenceRoutes_of_members
    source placement clauseMember literalMember]
  rw [taggedEqual]
  constructor
  · simpa [incidenceVertexPositionAt,
      List.getElem?_eq_getElem clauseIndexLt, clauseLookup]
  · simp [canonicalLiteralPosition, CNFIncidence.edge,
      PeriodicCNF.incidenceEdge]

/-- The canonical detours satisfy the complete incidence-graph endpoint
condition. -/
theorem orthogonalIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period) :
    (incidenceDrawing source placement
      (orthogonalIncidenceRoutes source placement)).RoutesMatch
        source.erase.incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges source.erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedIncidenceEqual⟩
  have endpoints :=
    orthogonalIncidenceRoutes_endpoints_of_tagged
      source placement taggedIncidenceMember
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
      source placement (orthogonalIncidenceRoutes source placement)
      endpointMembers.1
  have targetPosition :=
    incidenceDrawing_vertexPosition_of_mem
      source placement (orthogonalIncidenceRoutes source placement)
      endpointMembers.2
  have routeLookup :=
    incidenceDrawing_edgeRoute_of_tagged
      source placement (orthogonalIncidenceRoutes source placement)
      taggedIncidenceMember
  rw [← taggedIncidenceEqual]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition, CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition, CNFIncidence.edge_target]
    simp only [incidenceVertexPositionAt,
      PeriodicGridDrawing.periodTranslation]
    rw [incidenceDrawing_gridSize source placement
      (orthogonalIncidenceRoutes source placement) periodPositive]
    simpa [PeriodicVariablePlacement.translation] using endpoints.2

/-- Every route in the canonical incidence drawing is orthogonal. -/
theorem orthogonalIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (incidenceDrawing source placement
      (orthogonalIncidenceRoutes source placement)).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  change route ∈
    incidenceEdgeRoutes source
      (orthogonalIncidenceRoutes source placement) at routeMember
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
  rw [orthogonalIncidenceRoutes_of_members
    source placement clauseMember literalMember]
  exact orthogonalDetour_orthogonal _ _

end PositionedPeriodicCNF
end LeanTrominoes
