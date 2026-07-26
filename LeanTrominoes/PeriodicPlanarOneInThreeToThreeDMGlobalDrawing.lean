import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes
import LeanTrominoes.PeriodicPlanarThreeDM
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Global periodic grid drawing for the planar 3DM assembly

This file packages the globally assembled typed positions and incidence
routes as a `PeriodicGridDrawing`.  It then bridges the typed presentation
to the natural-number vertex and edge names of the encoded periodic 3DM
incidence graph.

The remaining separation, fundamental-square, and planarity obligations are
global geometric properties of the three-strand routing certificate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Pointwise position attached to a natural-number incidence-graph vertex.
The fallback is irrelevant for vertices occurring in the encoded graph. -/
def assembledVertexPositionAt
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    PeriodicThreeDMVertex → Cell
  | .triple index =>
      ((triples source)[index]?.map
        (assembledTriplePosition routing)).getD (0, 0)
  | .element .red atom =>
      ((redElements source)[atom]?.map
        (assembledRedElementPosition routing)).getD (0, 0)
  | .element .green atom =>
      ((greenElements source)[atom]?.map
        (assembledGreenElementPosition routing)).getD (0, 0)
  | .element .blue atom =>
      ((blueElements source)[atom]?.map
        (assembledBlueElementPosition routing)).getD (0, 0)

/-- Mapping indexed optional lookup over a complete numeric range recovers
the direct map over the source list. -/
theorem map_range_assembledPositionAt
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

/-- The assembled position list is pointwise mapping over the encoded
incidence graph's vertex presentation. -/
theorem assembledVertexPositions_eq_map
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    assembledVertexPositions routing =
      (encodedProblem source).incidenceGraph.vertices.map
        (assembledVertexPositionAt routing) := by
  unfold assembledVertexPositions
    PeriodicThreeDM.incidenceGraph
    PeriodicThreeDM.tripleVertices
    PeriodicThreeDM.elementVertices
    PeriodicThreeDM.coloredElementVertices
  simp only [List.map_append, List.map_map,
    encodedProblem, TypedProblem.encode, PeriodicThreeDM.elementCount,
    problem, List.length_map]
  simp only [Function.comp_def, assembledVertexPositionAt]
  rw [map_range_assembledPositionAt,
    map_range_assembledPositionAt,
    map_range_assembledPositionAt,
    map_range_assembledPositionAt]
  simp [List.append_assoc]

/-- The global typed lists packaged as a periodic grid drawing. -/
def assembledDrawing
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : PeriodicGridDrawing where
  gridSizePred := routing.period - 1
  vertexPositions := assembledVertexPositions routing
  edgeRoutes := assembledEdgeRoutes routing

/-- The grid drawing's positive side length is the routing certificate's
physical period. -/
theorem assembledDrawing_gridSize
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledDrawing routing).gridSize = routing.period := by
  change routing.period - 1 + 1 = routing.period
  have periodPositive := routing.periodPositive
  omega

/-- Semantic lattice offsets receive the same physical translation in the
routing certificate and its packaged drawing. -/
theorem assembledDrawing_periodTranslation
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) (offset : Cell) :
    (assembledDrawing routing).periodTranslation offset =
      routing.periodTranslation offset := by
  simp [PeriodicGridDrawing.periodTranslation,
    ThreeStrandRouting.periodTranslation,
    assembledDrawing_gridSize]

/-- Numeric triple lookup is the encoding of typed triple lookup at the
same presentation index. -/
theorem encodedProblem_triple_getElem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (index : Nat) (indexLt : index < (triples source).length) :
    (encodedProblem source).triples[index]'(by
      simpa [encodedProblem, TypedProblem.encode, problem] using indexLt) =
      (problem source).encodeTriple
        ((triples source)[index]'indexLt) := by
  simp [encodedProblem, TypedProblem.encode, problem]

/-- Looking up any listed encoded vertex recovers its pointwise assembled
position. -/
theorem assembledDrawing_vertexPosition_of_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember :
      vertex ∈ (encodedProblem source).incidenceGraph.vertices) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph vertex =
      assembledVertexPositionAt routing vertex := by
  have indexLt :
      (encodedProblem source).incidenceGraph.vertices.idxOf vertex <
        (encodedProblem source).incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  unfold PeriodicGridDrawing.vertexPosition
  change
    (assembledVertexPositions routing).getD
        ((encodedProblem source).incidenceGraph.vertices.idxOf vertex)
          (0, 0) =
      assembledVertexPositionAt routing vertex
  rw [assembledVertexPositions_eq_map]
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt)]
  simp only [List.getElem_map]
  apply congrArg (assembledVertexPositionAt routing)
  exact List.idxOf_get indexLt

/-- A valid numeric triple vertex retrieves the corresponding typed triple
position. -/
theorem assembledDrawing_triplePosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (index : Nat) (indexLt : index < (triples source).length) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph (.triple index) =
      assembledTriplePosition routing
        ((triples source)[index]'indexLt) := by
  rw [assembledDrawing_vertexPosition_of_mem routing]
  · simp [assembledVertexPositionAt,
      List.getElem?_eq_getElem indexLt]
  · simp [encodedProblem, TypedProblem.encode, problem,
      PeriodicThreeDM.incidenceGraph,
      PeriodicThreeDM.tripleVertices, indexLt]

/-- A listed typed red element's natural-number vertex retrieves its global
typed position. -/
theorem assembledDrawing_redElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (element : RedElement Variable)
    (elementMember : element ∈ redElements source) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph
        (.element .red ((redElements source).idxOf element)) =
      assembledRedElementPosition routing element := by
  rw [assembledDrawing_vertexPosition_of_mem routing]
  · simp [assembledVertexPositionAt,
      List.getElem?_idxOf elementMember]
  · have indexLt :=
      List.idxOf_lt_length_iff.mpr elementMember
    simp [encodedProblem, TypedProblem.encode, problem,
      PeriodicThreeDM.incidenceGraph,
      PeriodicThreeDM.elementVertices,
      PeriodicThreeDM.coloredElementVertices,
      PeriodicThreeDM.elementCount, indexLt]

/-- A listed typed green element's natural-number vertex retrieves its
global typed position. -/
theorem assembledDrawing_greenElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (element : GreenElement Variable)
    (elementMember : element ∈ greenElements source) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph
        (.element .green ((greenElements source).idxOf element)) =
      assembledGreenElementPosition routing element := by
  rw [assembledDrawing_vertexPosition_of_mem routing]
  · simp [assembledVertexPositionAt,
      List.getElem?_idxOf elementMember]
  · have indexLt :=
      List.idxOf_lt_length_iff.mpr elementMember
    simp [encodedProblem, TypedProblem.encode, problem,
      PeriodicThreeDM.incidenceGraph,
      PeriodicThreeDM.elementVertices,
      PeriodicThreeDM.coloredElementVertices,
      PeriodicThreeDM.elementCount, indexLt]

/-- A listed typed blue element's natural-number vertex retrieves its global
typed position. -/
theorem assembledDrawing_blueElementPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (element : BlueElement Variable)
    (elementMember : element ∈ blueElements source) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph
        (.element .blue ((blueElements source).idxOf element)) =
      assembledBlueElementPosition routing element := by
  rw [assembledDrawing_vertexPosition_of_mem routing]
  · simp [assembledVertexPositionAt,
      List.getElem?_idxOf elementMember]
  · have indexLt :=
      List.idxOf_lt_length_iff.mpr elementMember
    simp [encodedProblem, TypedProblem.encode, problem,
      PeriodicThreeDM.incidenceGraph,
      PeriodicThreeDM.elementVertices,
      PeriodicThreeDM.coloredElementVertices,
      PeriodicThreeDM.elementCount, indexLt]

/-- A genuine incidence tag retrieves its assembled route at the same
numeric index used by the encoded graph edge list. -/
theorem assembledDrawing_edgeRoute_at_tag
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember : tag ∈ (encodedProblem source).incidenceTags) :
    (assembledDrawing routing).edgeRoute
        ((encodedProblem source).incidenceTags.idxOf tag) =
      assembledRouteAtTag routing tag := by
  unfold PeriodicGridDrawing.edgeRoute assembledDrawing
  change
    ((encodedProblem source).incidenceTags.map
        (assembledRouteAtTag routing)).getD
      ((encodedProblem source).incidenceTags.idxOf tag) [] =
        assembledRouteAtTag routing tag
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf tagMember]
  rfl

/-- Direct in-range lookup of the tag-indexed assembled route list. -/
theorem assembledDrawing_edgeRoute_at_index
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (index : Nat)
    (indexLt :
      index < (encodedProblem source).incidenceTags.length) :
    (assembledDrawing routing).edgeRoute index =
      assembledRouteAtTag routing
        ((encodedProblem source).incidenceTags[index]'indexLt) := by
  unfold PeriodicGridDrawing.edgeRoute assembledDrawing
  change
    ((encodedProblem source).incidenceTags.map
      (assembledRouteAtTag routing)).getD index [] =
        assembledRouteAtTag routing
          ((encodedProblem source).incidenceTags[index]'indexLt)
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt)]
  simp only [List.getElem_map]

/-- At a genuine incidence tag, the numeric edge source position is the
position of the typed triple at that tag's index. -/
theorem assembledDrawing_incidenceSourcePosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember : tag ∈ (encodedProblem source).incidenceTags)
    (indexLt : tag.tripleIndex < (triples source).length) :
    (assembledDrawing routing).vertexPosition
        (encodedProblem source).incidenceGraph
        ((encodedProblem source).incidenceEdgeAt tag).source =
      assembledTriplePosition routing
        ((triples source)[tag.tripleIndex]'indexLt) := by
  rw [PeriodicThreeDM.incidenceEdgeAt_eq_of_tag_mem
    (encodedProblem source) tagMember]
  simp only [PeriodicThreeDM.incidenceEdge]
  exact assembledDrawing_triplePosition routing tag.tripleIndex indexLt

/-- At a genuine incidence tag, the translated numeric edge target is the
global target of the corresponding typed colored reference. -/
theorem assembledDrawing_incidenceTargetPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember : tag ∈ (encodedProblem source).incidenceTags)
    (indexLt : tag.tripleIndex < (triples source).length) :
    Cell.add
        ((assembledDrawing routing).vertexPosition
          (encodedProblem source).incidenceGraph
          ((encodedProblem source).incidenceEdgeAt tag).target)
        ((assembledDrawing routing).periodTranslation
          ((encodedProblem source).incidenceEdgeAt tag).offset) =
      assembledTypedReferenceTargetPosition routing
        ((triples source)[tag.tripleIndex]'indexLt) tag.color := by
  let triple := (triples source)[tag.tripleIndex]'indexLt
  have tripleMember : triple ∈ triples source :=
    List.getElem_mem indexLt
  have references := problem_isWellFormed source triple tripleMember
  rw [PeriodicThreeDM.incidenceEdgeAt_eq_of_tag_mem
    (encodedProblem source) tagMember]
  simp only [PeriodicThreeDM.incidenceEdge]
  rw [encodedProblem_triple_getElem source tag.tripleIndex indexLt]
  dsimp [triple] at references
  simp only [problem] at references ⊢
  cases tag.color with
  | red =>
      simp only [PeriodicThreeDMTriple.reference,
        TypedProblem.encodeTriple,
        encodeReference, assembledTypedReferenceTargetPosition]
      rw [assembledDrawing_redElementPosition routing _ references.1,
        assembledDrawing_periodTranslation]
  | green =>
      simp only [PeriodicThreeDMTriple.reference,
        TypedProblem.encodeTriple,
        encodeReference, assembledTypedReferenceTargetPosition]
      rw [assembledDrawing_greenElementPosition routing _ references.2.1,
        assembledDrawing_periodTranslation]
  | blue =>
      simp only [PeriodicThreeDMTriple.reference,
        TypedProblem.encodeTriple,
        encodeReference, assembledTypedReferenceTargetPosition]
      rw [assembledDrawing_blueElementPosition routing _ references.2.2,
        assembledDrawing_periodTranslation]

/-- A genuine incidence tag has the required numeric graph endpoints at its
tag-list route index. -/
theorem assembledDrawing_incidenceRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember : tag ∈ (encodedProblem source).incidenceTags) :
    ((assembledDrawing routing).edgeRoute
          ((encodedProblem source).incidenceTags.idxOf tag)).head? =
        some ((assembledDrawing routing).vertexPosition
          (encodedProblem source).incidenceGraph
          ((encodedProblem source).incidenceEdgeAt tag).source) ∧
      ((assembledDrawing routing).edgeRoute
          ((encodedProblem source).incidenceTags.idxOf tag)).getLast? =
        some (Cell.add
          ((assembledDrawing routing).vertexPosition
            (encodedProblem source).incidenceGraph
            ((encodedProblem source).incidenceEdgeAt tag).target)
          ((assembledDrawing routing).periodTranslation
            ((encodedProblem source).incidenceEdgeAt tag).offset)) := by
  have indexLt : tag.tripleIndex < (triples source).length := by
    simpa [encodedProblem, TypedProblem.encode, problem] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem source) tagMember
  rw [assembledDrawing_edgeRoute_at_tag routing tag tagMember]
  have endpoints :=
    assembledRouteAtTag_endpoints routing tag tagMember
  constructor
  · exact endpoints.1.trans (congrArg some
      (assembledDrawing_incidenceSourcePosition
        routing tag tagMember indexLt).symm)
  · exact endpoints.2.trans (congrArg some
      (assembledDrawing_incidenceTargetPosition
        routing tag tagMember indexLt).symm)

/-- The assembled numeric routes match all encoded incidence-graph
endpoints. -/
theorem assembledDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledDrawing routing).RoutesMatch
      (encodedProblem source).incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have mappedMember := taggedEdgeMember
  rw [PeriodicThreeDM.incidenceGraph_edges_eq_tags_map]
    at mappedMember
  have indexLt :
      taggedEdge.2 <
        (encodedProblem source).incidenceTags.length := by
    simpa using List.snd_lt_of_mem_zipIdx mappedMember
  let tag :=
    (encodedProblem source).incidenceTags[taggedEdge.2]'indexLt
  have tagMember :
      tag ∈ (encodedProblem source).incidenceTags :=
    List.getElem_mem indexLt
  have edgeEq :
      (encodedProblem source).incidenceEdgeAt tag =
        taggedEdge.1 := by
    have valueAt := (List.mem_zipIdx' mappedMember).2.symm
    simpa [tag] using valueAt
  have tripleIndexLt :
      tag.tripleIndex < (triples source).length := by
    simpa [encodedProblem, TypedProblem.encode, problem] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem source) tagMember
  rw [assembledDrawing_edgeRoute_at_index
    routing taggedEdge.2 indexLt, ← edgeEq]
  have endpoints :=
    assembledRouteAtTag_endpoints routing tag tagMember
  constructor
  · exact endpoints.1.trans (congrArg some
      (assembledDrawing_incidenceSourcePosition
        routing tag tagMember tripleIndexLt).symm)
  · exact endpoints.2.trans (congrArg some
      (assembledDrawing_incidenceTargetPosition
        routing tag tagMember tripleIndexLt).symm)

/-- Every route in the assembled numeric drawing remains rectilinear. -/
theorem assembledDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledDrawing routing).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  simp only [assembledDrawing] at routeMember
  rcases List.mem_map.mp routeMember with ⟨tag, _, rfl⟩
  exact assembledRouteAtTag_orthogonal routing tag

/-- The genuinely global geometric obligations left after local gadget and
numeric endpoint verification. -/
structure AssemblyGeometry
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : Prop where
  positionsNodup :
    (assembledVertexPositions routing).Nodup
  positionsInside :
    ∀ position ∈ assembledVertexPositions routing,
      (assembledDrawing routing).PositionInFundamentalSquare position
  planar :
    (assembledDrawing routing).IsPlanar

/-- A global geometry certificate completes every finite compatibility
obligation for the assembled encoded incidence drawing. -/
theorem assembledDrawing_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (geometry : AssemblyGeometry routing) :
    (assembledDrawing routing).IsCompatible
      (encodedProblem source).incidenceGraph := by
  refine ⟨?_, assembledVertexPositions_length routing,
    assembledEdgeRoutes_length routing, geometry.positionsNodup,
    geometry.positionsInside, assembledDrawing_routesMatch routing⟩
  exact PeriodicThreeDM.incidenceGraph_isWellFormed
    (encodedProblem source) (encodedProblem_isWellFormed source)

/-- Package a three-strand routing and its global geometry certificate as a
certified planar presentation of the encoded periodic 3DM problem. -/
def assembledPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (geometry : AssemblyGeometry routing) :
    (encodedProblem source).PlanarPresentation where
  drawing := assembledDrawing routing
  problemWellFormed := encodedProblem_isWellFormed source
  compatible := assembledDrawing_isCompatible routing geometry
  orthogonal := assembledDrawing_isOrthogonal routing
  planar := geometry.planar

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
