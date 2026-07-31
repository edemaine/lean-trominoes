import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing
import LeanTrominoes.PeriodicCNFPlanarIncidences
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Pointwise lookup in positioned periodic incidence drawings

The finite drawing certificate stores vertex positions and edge routes as
flat lists, while the planar 3DM replacement addresses one syntactic literal
at a time.  This file proves the exact bridge between those views.

Every metadata-rich `(clause, literal)` occurrence retrieves:

* the displayed variable and canonical clause positions at its endpoints;
* the route supplied at its clause and literal indices; and
* the expected source and translated-target endpoint equations.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Two distinct points in the open fundamental square cannot become equal
after translating one by an integral drawing period. -/
theorem fundamentalPosition_ne_translated
    (drawing : PeriodicGridDrawing)
    {first second translate : Cell}
    (firstBounds :
      drawing.PositionInFundamentalSquare first)
    (secondBounds :
      drawing.PositionInFundamentalSquare second)
    (different : first ≠ second) :
    first ≠
      Cell.add second
        (drawing.periodTranslation translate) := by
  intro equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases translate with ⟨translateX, translateY⟩
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare] at firstBounds secondBounds
  simp only [Cell.add, PeriodicGridDrawing.periodTranslation,
    Cell.scale, Prod.mk.injEq] at equal
  have periodPositive :
      (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have translateXZero : translateX = 0 := by
    by_contra nonzero
    have cases : translateX ≤ -1 ∨ 1 ≤ translateX := by
      omega
    rcases cases with negative | positive
    · have productBound :=
        mul_le_mul_of_nonneg_left negative
          (le_of_lt periodPositive)
      norm_num at productBound
      omega
    · have productBound :=
        mul_le_mul_of_nonneg_left positive
          (le_of_lt periodPositive)
      norm_num at productBound
      omega
  have translateYZero : translateY = 0 := by
    by_contra nonzero
    have cases : translateY ≤ -1 ∨ 1 ≤ translateY := by
      omega
    rcases cases with negative | positive
    · have productBound :=
        mul_le_mul_of_nonneg_left negative
          (le_of_lt periodPositive)
      norm_num at productBound
      omega
    · have productBound :=
        mul_le_mul_of_nonneg_left positive
          (le_of_lt periodPositive)
      norm_num at productBound
      omega
  subst translateX
  subst translateY
  simp only [mul_zero, add_zero] at equal
  exact different (Prod.ext equal.1 equal.2)

/-- Total pointwise description of the vertex-position list used by a
positioned incidence drawing. -/
def incidenceVertexPositionAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    CNFVertex Variable → Cell
  | .variable atom => placement.position atom
  | .clause clauseIndex =>
      (source.clauses[clauseIndex]?.map fun clause =>
        canonicalClausePosition placement clause).getD (0, 0)

/-- Mapping optional indexed lookup over a complete numeric range recovers
the direct map over the list. -/
theorem map_range_getElem?_getD
    {α β : Type*} (values : List α) (function : α → β)
    (default : β) :
    (List.range values.length).map (fun index =>
      (values[index]?.map function).getD default) =
        values.map function := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    have indexBound : index < values.length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem indexBound]
    rfl

/-- The stored vertex-position list is pointwise mapping over the incidence
graph's vertex presentation. -/
theorem incidenceVertexPositions_eq_map
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    incidenceVertexPositions source placement =
      source.erase.incidenceGraph.vertices.map
        (incidenceVertexPositionAt source placement) := by
  unfold incidenceVertexPositions
    PeriodicCNF.incidenceGraph
  rw [List.map_append]
  congr 1
  · simp [PeriodicCNF.incidenceVariableVertices,
      incidenceVertexPositionAt]
  · unfold PeriodicCNF.incidenceClauseVertices
    rw [List.map_map]
    change
      source.clauses.map
          (canonicalClausePosition placement) =
        (List.range source.erase.clauses.length).map
          (fun index =>
            (source.clauses[index]?.map fun clause =>
              canonicalClausePosition placement clause).getD
                (0, 0))
    rw [show source.erase.clauses.length =
        source.clauses.length by
      simp [PositionedPeriodicCNF.erase]]
    exact
      (map_range_getElem?_getD source.clauses
        (canonicalClausePosition placement) (0, 0)).symm

/-- Looking up any listed incidence-graph vertex recovers its pointwise
position. -/
theorem incidenceDrawing_vertexPosition_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {vertex : CNFVertex Variable}
    (vertexMember : vertex ∈ source.erase.incidenceGraph.vertices) :
    (incidenceDrawing source placement routes).vertexPosition
        source.erase.incidenceGraph vertex =
      incidenceVertexPositionAt source placement vertex := by
  have indexLt :
      source.erase.incidenceGraph.vertices.idxOf vertex <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  unfold PeriodicGridDrawing.vertexPosition
  change
    (incidenceVertexPositions source placement).getD
        (source.erase.incidenceGraph.vertices.idxOf vertex) (0, 0) =
      incidenceVertexPositionAt source placement vertex
  rw [incidenceVertexPositions_eq_map]
  rw [List.getD_eq_getElem _ _
    (by simpa using indexLt)]
  simp only [List.getElem_map]
  apply congrArg (incidenceVertexPositionAt source placement)
  exact List.idxOf_get indexLt

/-- Compatibility alone makes every listed graph vertex position an actual
member of the stored drawing-position list. -/
theorem incidenceDrawing_vertexPosition_mem_of_compatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (compatible :
      (incidenceDrawing source placement routes).IsCompatible
        source.erase.incidenceGraph)
    {vertex : CNFVertex Variable}
    (vertexMember : vertex ∈ source.erase.incidenceGraph.vertices) :
    (incidenceDrawing source placement routes).vertexPosition
        source.erase.incidenceGraph vertex ∈
      (incidenceDrawing source placement routes).vertexPositions := by
  have indexLt :
      source.erase.incidenceGraph.vertices.idxOf vertex <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  have positionIndexLt :
      source.erase.incidenceGraph.vertices.idxOf vertex <
        (incidenceDrawing source placement routes).vertexPositions.length := by
    rwa [compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition
  rw [List.getD_eq_getElem _ _ positionIndexLt]
  exact List.getElem_mem positionIndexLt

/-- Compatibility makes stored drawing positions injective on the listed
incidence-graph vertices. -/
theorem incidenceDrawing_vertexPosition_injective_on_of_compatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (compatible :
      (incidenceDrawing source placement routes).IsCompatible
        source.erase.incidenceGraph)
    {first second : CNFVertex Variable}
    (firstMember :
      first ∈ source.erase.incidenceGraph.vertices)
    (secondMember :
      second ∈ source.erase.incidenceGraph.vertices)
    (equal :
      (incidenceDrawing source placement routes).vertexPosition
          source.erase.incidenceGraph first =
        (incidenceDrawing source placement routes).vertexPosition
          source.erase.incidenceGraph second) :
    first = second := by
  have firstIndexLt :
      source.erase.incidenceGraph.vertices.idxOf first <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr firstMember
  have secondIndexLt :
      source.erase.incidenceGraph.vertices.idxOf second <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr secondMember
  have firstPositionLt :
      source.erase.incidenceGraph.vertices.idxOf first <
        (incidenceDrawing source placement routes).vertexPositions.length := by
    rwa [compatible.2.1]
  have secondPositionLt :
      source.erase.incidenceGraph.vertices.idxOf second <
        (incidenceDrawing source placement routes).vertexPositions.length := by
    rwa [compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition at equal
  rw [List.getD_eq_getElem _ _ firstPositionLt,
    List.getD_eq_getElem _ _ secondPositionLt] at equal
  have indicesEqual :
      source.erase.incidenceGraph.vertices.idxOf first =
        source.erase.incidenceGraph.vertices.idxOf second :=
    (compatible.2.2.2.1.getElem_inj_iff).mp equal
  calc
    first =
        source.erase.incidenceGraph.vertices[
          source.erase.incidenceGraph.vertices.idxOf first]'firstIndexLt :=
      (List.idxOf_get firstIndexLt).symm
    _ =
        source.erase.incidenceGraph.vertices[
          source.erase.incidenceGraph.vertices.idxOf second]'secondIndexLt := by
      congr
    _ = second :=
      List.idxOf_get secondIndexLt

/-- Looking up a listed incidence vertex returns an actual member of the
stored drawing-position list. -/
theorem PlanarIncidencePresentation.vertexPosition_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {vertex : CNFVertex Variable}
    (vertexMember :
      vertex ∈ source.erase.incidenceGraph.vertices) :
    (incidenceDrawing source placement
      presentation.routes).vertexPosition
        source.erase.incidenceGraph vertex ∈
      (incidenceDrawing source placement
        presentation.routes).vertexPositions := by
  have indexLt :
      source.erase.incidenceGraph.vertices.idxOf vertex <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  have positionIndexLt :
      source.erase.incidenceGraph.vertices.idxOf vertex <
        (incidenceDrawing source placement
          presentation.routes).vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition
  rw [List.getD_eq_getElem _ _ positionIndexLt]
  exact List.getElem_mem positionIndexLt

/-- Certified drawing positions are injective on the listed incidence-graph
vertices. -/
theorem PlanarIncidencePresentation.vertexPosition_injective_on
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {first second : CNFVertex Variable}
    (firstMember :
      first ∈ source.erase.incidenceGraph.vertices)
    (secondMember :
      second ∈ source.erase.incidenceGraph.vertices)
    (equal :
      (incidenceDrawing source placement
        presentation.routes).vertexPosition
          source.erase.incidenceGraph first =
        (incidenceDrawing source placement
          presentation.routes).vertexPosition
          source.erase.incidenceGraph second) :
    first = second := by
  have firstIndexLt :
      source.erase.incidenceGraph.vertices.idxOf first <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr firstMember
  have secondIndexLt :
      source.erase.incidenceGraph.vertices.idxOf second <
        source.erase.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr secondMember
  have firstPositionLt :
      source.erase.incidenceGraph.vertices.idxOf first <
        (incidenceDrawing source placement
          presentation.routes).vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  have secondPositionLt :
      source.erase.incidenceGraph.vertices.idxOf second <
        (incidenceDrawing source placement
          presentation.routes).vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition at equal
  rw [List.getD_eq_getElem _ _ firstPositionLt,
    List.getD_eq_getElem _ _ secondPositionLt] at equal
  have indicesEqual :
      source.erase.incidenceGraph.vertices.idxOf first =
        source.erase.incidenceGraph.vertices.idxOf second :=
    (presentation.compatible.2.2.2.1.getElem_inj_iff).mp equal
  calc
    first =
        source.erase.incidenceGraph.vertices[
          source.erase.incidenceGraph.vertices.idxOf first]'firstIndexLt :=
      (List.idxOf_get firstIndexLt).symm
    _ =
        source.erase.incidenceGraph.vertices[
          source.erase.incidenceGraph.vertices.idxOf second]'secondIndexLt := by
      congr
    _ = second :=
      List.idxOf_get secondIndexLt

/-- A genuine positioned clause index retrieves its canonical clause
position. -/
@[simp]
theorem incidenceVertexPositionAt_clause
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    incidenceVertexPositionAt source placement (.clause clauseIndex) =
      canonicalClausePosition placement source.clauses[clauseIndex] := by
  simp [incidenceVertexPositionAt,
    List.getElem?_eq_getElem indexLt]

/-- The flat route list is the metadata incidence list mapped to the route at
the same clause and literal indices. -/
theorem incidenceEdgeRoutes_eq_metadata_map
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    incidenceEdgeRoutes source routes =
      (PeriodicCNF.incidencesWithMetadata source.erase).map
        (fun incidence =>
          routes incidence.clauseIndex incidence.literalIndex) := by
  unfold incidenceEdgeRoutes
    PeriodicCNF.incidencesWithMetadata
    PositionedPeriodicCNF.erase
  rw [List.zipIdx_map]
  simp only [List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, Prod.map, id_eq]

/-- A tagged metadata incidence retrieves precisely its declared route from
the flat drawing route list. -/
theorem incidenceDrawing_edgeRoute_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (incidenceDrawing source placement routes).edgeRoute tagged.2 =
      routes tagged.1.clauseIndex tagged.1.literalIndex := by
  have mappedMember :
      (routes tagged.1.clauseIndex tagged.1.literalIndex,
        tagged.2) ∈
        ((PeriodicCNF.incidencesWithMetadata source.erase).map
          (fun incidence =>
            routes incidence.clauseIndex
              incidence.literalIndex)).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨tagged, taggedMember, by cases tagged; rfl⟩
  unfold PeriodicGridDrawing.edgeRoute
    incidenceDrawing
  rw [incidenceEdgeRoutes_eq_metadata_map]
  have indexLt :
      tagged.2 <
        ((PeriodicCNF.incidencesWithMetadata source.erase).map
          (fun incidence =>
            routes incidence.clauseIndex
              incidence.literalIndex)).length :=
    List.snd_lt_of_mem_zipIdx mappedMember
  rw [List.getD_eq_getElem _ _ indexLt]
  exact (List.mem_zipIdx' mappedMember).2.symm

/-- A tagged flattened incidence retains the positioned clause and literal
from which all four metadata fields were built. -/
theorem incidenceMetadata_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    ∃ positionedClause : PositionedPeriodicClause Variable,
      ∃ literal : PeriodicLiteral Variable,
        (positionedClause, tagged.1.clauseIndex) ∈
            source.clauses.zipIdx ∧
          (literal, tagged.1.literalIndex) ∈
            positionedClause.literals.zipIdx ∧
          tagged.1 =
            ⟨tagged.1.clauseIndex, positionedClause.literals,
              tagged.1.literalIndex, literal⟩ := by
  have incidenceMember :
      tagged.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx taggedMember
  unfold PeriodicCNF.incidencesWithMetadata
    PositionedPeriodicCNF.erase at incidenceMember
  rw [List.zipIdx_map] at incidenceMember
  simp only [List.mem_flatMap, List.mem_map] at incidenceMember
  rcases incidenceMember with
    ⟨mappedTaggedClause, mappedTaggedClauseMember,
      taggedLiteral, taggedLiteralMember, incidenceEq⟩
  rcases mappedTaggedClauseMember with
    ⟨taggedClause, taggedClauseMember, mappedTaggedClauseEq⟩
  subst mappedTaggedClause
  rcases taggedClause with ⟨positionedClause, clauseIndex⟩
  rcases taggedLiteral with ⟨literal, literalIndex⟩
  simp only [Prod.map, id_eq] at taggedClauseMember taggedLiteralMember incidenceEq
  rw [← incidenceEq]
  exact
    ⟨positionedClause, literal,
      taggedClauseMember, taggedLiteralMember, rfl⟩

/-- Compatibility gives the exact endpoints of every pointwise route
selected by a tagged syntactic incidence. -/
theorem PlanarIncidencePresentation.route_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (incidenceVertexPositionAt source placement
            (.clause tagged.1.clauseIndex)) ∧
      (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some (Cell.add
          (placement.position tagged.1.literal.atom)
          ((incidenceDrawing source placement
            presentation.routes).periodTranslation
              tagged.1.edge.offset)) := by
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have endpointMembers :=
    presentation.compatible.1.2 tagged.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have endpoints :=
    presentation.compatible.2.2.2.2.2
      (tagged.1.edge, tagged.2) edgeMember
  rw [incidenceDrawing_edgeRoute_of_tagged
      source placement presentation.routes taggedMember] at endpoints
  rw [incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes endpointMembers.1,
    incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes endpointMembers.2] at endpoints
  simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge,
    incidenceVertexPositionAt] using endpoints

/-- The clause and translated-variable endpoints of every genuine incidence
route are distinct. -/
theorem PlanarIncidencePresentation.route_endpoints_ne_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    incidenceVertexPositionAt source placement
          (.clause tagged.1.clauseIndex) ≠
      Cell.add
        (placement.position tagged.1.literal.atom)
        ((incidenceDrawing source placement
          presentation.routes).periodTranslation
            tagged.1.edge.offset) := by
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have endpointMembers :=
    presentation.compatible.1.2 tagged.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have sourceLookup :=
    incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes endpointMembers.1
  have targetLookup :=
    incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes endpointMembers.2
  have sourceLookup' :
      (incidenceDrawing source placement
        presentation.routes).vertexPosition
          source.erase.incidenceGraph
          (.clause tagged.1.clauseIndex) =
        incidenceVertexPositionAt source placement
          (.clause tagged.1.clauseIndex) := by
    simpa only [CNFIncidence.edge_source] using sourceLookup
  have targetLookup' :
      (incidenceDrawing source placement
        presentation.routes).vertexPosition
          source.erase.incidenceGraph
          (.variable tagged.1.literal.atom) =
        placement.position tagged.1.literal.atom := by
    simpa only [CNFIncidence.edge_target,
      incidenceVertexPositionAt] using targetLookup
  have sourcePositionMember :=
    presentation.vertexPosition_mem endpointMembers.1
  have targetPositionMember :=
    presentation.vertexPosition_mem endpointMembers.2
  have sourceBounds :
      drawing.PositionInFundamentalSquare
        (incidenceVertexPositionAt source placement
          (.clause tagged.1.clauseIndex)) := by
    rw [← sourceLookup']
    exact presentation.compatible.2.2.2.2.1 _
      sourcePositionMember
  have targetBounds :
      drawing.PositionInFundamentalSquare
        (placement.position tagged.1.literal.atom) := by
    rw [← targetLookup']
    exact presentation.compatible.2.2.2.2.1 _
      targetPositionMember
  apply fundamentalPosition_ne_translated
    drawing sourceBounds targetBounds
  intro prototypePositionsEqual
  have verticesEqual :=
    presentation.vertexPosition_injective_on
      endpointMembers.1 endpointMembers.2
      (sourceLookup'.trans
        (prototypePositionsEqual.trans targetLookup'.symm))
  cases verticesEqual

/-- Every genuine incidence route contains at least one segment. -/
theorem PlanarIncidencePresentation.route_segments_ne_nil_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    gridPolylineSegments
        (presentation.routes
          tagged.1.clauseIndex tagged.1.literalIndex) ≠ [] := by
  have endpoints :=
    presentation.route_endpoints_of_tagged taggedMember
  have endpointDifferent :=
    presentation.route_endpoints_ne_of_tagged taggedMember
  generalize
      presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex = route at endpoints ⊢
  cases route with
  | nil =>
      simp at endpoints
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [List.head?_singleton, List.getLast?_singleton,
            Option.some.injEq] at endpoints
          exact
            (endpointDifferent
              (endpoints.1.symm.trans endpoints.2)).elim
      | cons second rest =>
          simp [gridPolylineSegments]

/-- Every actual pointwise incidence route occurs in the certified drawing's
flat route list. -/
theorem PlanarIncidencePresentation.route_mem_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex ∈
      (incidenceDrawing source placement
        presentation.routes).edgeRoutes := by
  change
    presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex ∈
      incidenceEdgeRoutes source presentation.routes
  rw [incidenceEdgeRoutes_eq_metadata_map]
  exact List.mem_map.mpr
    ⟨tagged.1, List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩

/-- Every actual pointwise incidence route in a certified presentation is an
orthogonal polyline. -/
theorem PlanarIncidencePresentation.route_orthogonal_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex) := by
  exact
    (PeriodicGridDrawing.isOrthogonal_iff_routes
      (incidenceDrawing source placement
        presentation.routes)).mp presentation.orthogonal _
      (presentation.route_mem_of_tagged taggedMember)

end PositionedPeriodicCNF
end LeanTrominoes
