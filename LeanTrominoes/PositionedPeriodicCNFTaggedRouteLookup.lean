import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Tagged route lookup in positioned periodic incidence drawings

The route list of an incidence drawing is a map over its metadata-rich
incidence enumeration.  This module preserves the global flat route index
while recovering the corresponding positioned clause and literal
coordinates.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A tagged metadata incidence occurs at the same numeric index in the
flat route list of the positioned incidence drawing. -/
theorem taggedRoute_mem_of_taggedIncidence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {taggedIncidence : CNFIncidence Variable × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (routes taggedIncidence.1.clauseIndex
        taggedIncidence.1.literalIndex,
      taggedIncidence.2) ∈
        (incidenceDrawing source placement routes).edgeRoutes.zipIdx := by
  change
    (routes taggedIncidence.1.clauseIndex
        taggedIncidence.1.literalIndex,
      taggedIncidence.2) ∈
      (incidenceEdgeRoutes source routes).zipIdx
  rw [incidenceEdgeRoutes_eq_metadata_map,
    List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨taggedIncidence, taggedIncidenceMember,
      by cases taggedIncidence; rfl⟩

/-- In any compatible positioned drawing, the head of one genuine incidence
route cannot equal the tail of another.  The former is a clause-vertex lift
and the latter is a variable-vertex lift, which remain distinct under every
period translation. -/
theorem route_head_ne_route_last_of_taggedIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (compatible :
      (incidenceDrawing source placement routes).IsCompatible
        source.erase.incidenceGraph)
    {first second : CNFIncidence Variable × Nat}
    (firstMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (secondMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (routes first.1.clauseIndex first.1.literalIndex).head? ≠
      (routes second.1.clauseIndex second.1.literalIndex).getLast? := by
  let drawing := incidenceDrawing source placement routes
  have firstEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase firstMember
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondMember
  have firstEndpointMembers :=
    compatible.1.2 first.1.edge
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
  have secondEndpointMembers :=
    compatible.1.2 second.1.edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have firstEndpoints :=
    compatible.2.2.2.2.2
      (first.1.edge, first.2) firstEdgeMember
  have secondEndpoints :=
    compatible.2.2.2.2.2
      (second.1.edge, second.2) secondEdgeMember
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement routes firstMember] at firstEndpoints
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement routes secondMember] at secondEndpoints
  have sourceMember :
      first.1.edge.source ∈
        source.erase.incidenceGraph.vertices :=
    firstEndpointMembers.1
  have targetMember :
      second.1.edge.target ∈
        source.erase.incidenceGraph.vertices :=
    secondEndpointMembers.2
  have sourcePositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement routes compatible sourceMember
  have targetPositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement routes compatible targetMember
  have sourceBounds :
      drawing.PositionInFundamentalSquare
        (drawing.vertexPosition
          source.erase.incidenceGraph first.1.edge.source) :=
    compatible.2.2.2.2.1 _
      sourcePositionMember
  have targetBounds :
      drawing.PositionInFundamentalSquare
        (drawing.vertexPosition
          source.erase.incidenceGraph second.1.edge.target) :=
    compatible.2.2.2.2.1 _
      targetPositionMember
  have sourceTargetDifferent :
      drawing.vertexPosition
          source.erase.incidenceGraph first.1.edge.source ≠
        drawing.vertexPosition
          source.erase.incidenceGraph second.1.edge.target := by
    intro positionsEqual
    have verticesEqual :=
      incidenceDrawing_vertexPosition_injective_on_of_compatible
        source placement routes compatible
        sourceMember targetMember positionsEqual
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      verticesEqual
  have liftedDifferent :=
    fundamentalPosition_ne_translated
      drawing (translate := second.1.edge.offset)
      sourceBounds targetBounds sourceTargetDifferent
  rw [firstEndpoints.1, secondEndpoints.2]
  exact fun equal => liftedDifferent (Option.some.inj equal)

/-- The head of one genuine incidence route also differs from the tail of
any periodic translate of another genuine incidence route. -/
theorem route_head_ne_translated_route_last_of_taggedIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (compatible :
      (incidenceDrawing source placement routes).IsCompatible
        source.erase.incidenceGraph)
    {first second : CNFIncidence Variable × Nat}
    (firstMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (secondMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (relativeTranslate : Cell) :
    (routes first.1.clauseIndex first.1.literalIndex).head? ≠
      ((routes second.1.clauseIndex second.1.literalIndex).map
        (Cell.add
          ((incidenceDrawing source placement routes).periodTranslation
            relativeTranslate))).getLast? := by
  let drawing := incidenceDrawing source placement routes
  have firstEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase firstMember
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondMember
  have firstEndpointMembers :=
    compatible.1.2 first.1.edge
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
  have secondEndpointMembers :=
    compatible.1.2 second.1.edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have firstEndpoints :=
    compatible.2.2.2.2.2
      (first.1.edge, first.2) firstEdgeMember
  have secondEndpoints :=
    compatible.2.2.2.2.2
      (second.1.edge, second.2) secondEdgeMember
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement routes firstMember] at firstEndpoints
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement routes secondMember] at secondEndpoints
  have sourceMember :
      first.1.edge.source ∈
        source.erase.incidenceGraph.vertices :=
    firstEndpointMembers.1
  have targetMember :
      second.1.edge.target ∈
        source.erase.incidenceGraph.vertices :=
    secondEndpointMembers.2
  have sourcePositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement routes compatible sourceMember
  have targetPositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement routes compatible targetMember
  have sourceBounds :
      drawing.PositionInFundamentalSquare
        (drawing.vertexPosition
          source.erase.incidenceGraph first.1.edge.source) :=
    compatible.2.2.2.2.1 _ sourcePositionMember
  have targetBounds :
      drawing.PositionInFundamentalSquare
        (drawing.vertexPosition
          source.erase.incidenceGraph second.1.edge.target) :=
    compatible.2.2.2.2.1 _ targetPositionMember
  have sourceTargetDifferent :
      drawing.vertexPosition
          source.erase.incidenceGraph first.1.edge.source ≠
        drawing.vertexPosition
          source.erase.incidenceGraph second.1.edge.target := by
    intro positionsEqual
    have verticesEqual :=
      incidenceDrawing_vertexPosition_injective_on_of_compatible
        source placement routes compatible
        sourceMember targetMember positionsEqual
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      verticesEqual
  have liftedDifferent :=
    fundamentalPosition_ne_translated
      drawing
      (translate := Cell.add second.1.edge.offset relativeTranslate)
      sourceBounds targetBounds sourceTargetDifferent
  rw [firstEndpoints.1, List.getLast?_map, secondEndpoints.2]
  intro equal
  apply liftedDifferent
  have pointEqual := Option.some.inj equal
  exact pointEqual.trans (by
    apply Prod.ext <;>
      simp [drawing, PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale] <;>
      ring)

/-- Every genuine positioned clause/literal incidence supplies both its
metadata tag and its route at one common flat drawing index. -/
theorem exists_taggedIncidenceRoute_of_positioned_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ routeIndex : Nat,
      ((⟨clauseIndex, clause.literals, literalIndex, literal⟩ :
          CNFIncidence Variable),
        routeIndex) ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx ∧
      (routes clauseIndex literalIndex, routeIndex) ∈
          (incidenceDrawing source placement routes).edgeRoutes.zipIdx := by
  let incidence : CNFIncidence Variable :=
    ⟨clauseIndex, clause.literals, literalIndex, literal⟩
  have erasedClauseMember :
      (clause.literals, clauseIndex) ∈
        source.erase.clauses.zipIdx := by
    change
      (clause.literals, clauseIndex) ∈
        (source.clauses.map
          PositionedPeriodicClause.literals).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have incidenceMember :
      incidence ∈
        PeriodicCNF.incidencesWithMetadata source.erase := by
    exact
      (PeriodicCNF.mem_incidencesWithMetadata_iff
        source.erase incidence).mpr
        ⟨erasedClauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceLookup⟩
  let taggedIncidence : CNFIncidence Variable × Nat :=
    (incidence, incidenceIndex)
  have taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          source.erase).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa [taggedIncidence,
      List.getElem?_eq_getElem incidenceIndex.isLt] using
      congrArg some incidenceLookup
  refine ⟨taggedIncidence.2, ?_, ?_⟩
  · simpa [taggedIncidence, incidence] using
      taggedIncidenceMember
  · simpa [taggedIncidence, incidence] using
      taggedRoute_mem_of_taggedIncidence
        source placement routes taggedIncidenceMember

/-- Every genuine positioned clause/literal incidence supplies its route
with the corresponding flat drawing index. -/
theorem exists_taggedRoute_of_positioned_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ routeIndex : Nat,
      (routes clauseIndex literalIndex, routeIndex) ∈
        (incidenceDrawing source placement routes).edgeRoutes.zipIdx := by
  rcases
      exists_taggedIncidenceRoute_of_positioned_members
        source placement routes clauseMember literalMember with
    ⟨routeIndex, _taggedIncidenceMember, routeMember⟩
  exact ⟨routeIndex, routeMember⟩

/-- A route occurrence tagged in the flat drawing list recovers the
metadata-rich incidence at the same flat index and its two presentation
coordinates. -/
theorem exists_incidenceCoordinates_of_taggedRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (taggedRoute : List Cell × Nat)
    (taggedRouteMember :
      taggedRoute ∈
        (incidenceDrawing source placement routes).edgeRoutes.zipIdx) :
    ∃ taggedIncidence :
        CNFIncidence Variable × Nat,
      taggedIncidence ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx ∧
        ∃ positionedClause : PositionedPeriodicClause Variable,
          ∃ literal : PeriodicLiteral Variable,
            (positionedClause,
                taggedIncidence.1.clauseIndex) ∈
              source.clauses.zipIdx ∧
            (literal, taggedIncidence.1.literalIndex) ∈
              positionedClause.literals.zipIdx ∧
            taggedRoute.1 =
              routes taggedIncidence.1.clauseIndex
                taggedIncidence.1.literalIndex ∧
            taggedIncidence.2 = taggedRoute.2 := by
  change
    taggedRoute ∈
      (incidenceEdgeRoutes source routes).zipIdx
      at taggedRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    List.zipIdx_map] at taggedRouteMember
  rcases List.mem_map.mp taggedRouteMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedRouteEq⟩
  rcases incidenceMetadata_of_tagged
      source taggedIncidenceMember with
    ⟨positionedClause, literal,
      positionedClauseMember, literalMember, _⟩
  exact
    ⟨taggedIncidence, taggedIncidenceMember,
      positionedClause, literal,
      positionedClauseMember, literalMember,
      (congrArg Prod.fst taggedRouteEq).symm,
      congrArg Prod.snd taggedRouteEq⟩

end PositionedPeriodicCNF
end LeanTrominoes
