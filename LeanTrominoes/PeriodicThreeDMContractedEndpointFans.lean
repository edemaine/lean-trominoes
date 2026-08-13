/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DegreeThreeVertexNormalizationFans
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-!
# Endpoint fans of the contracted periodic 3DM drawing

This module turns each source or target end of an executable contracted edge
into the local datum consumed by degree-three normalization.  The outward
direction is the first route direction at a source and the opposite of the
last route direction at a target.  Compatibility, the degree promise, and
orthogonality prove that all of these total direction lookups are genuine.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- One syntactic end of a contracted edge.  Keeping the edge value in the
constructor makes the enumeration executable without dependent indices. -/
inductive ContractedEndpoint
  | source (edge : ContractedEdge)
  | target (edge : ContractedEdge)
  deriving DecidableEq, Repr

namespace ContractedEndpoint

/-- Contracted edge owning this endpoint. -/
def edge : ContractedEndpoint → ContractedEdge
  | .source edge | .target edge => edge

/-- Prototype vertex at this endpoint. -/
def vertex : ContractedEndpoint → PeriodicThreeDMVertex
  | .source edge => edge.toPeriodicEdge.source
  | .target edge => edge.toPeriodicEdge.target

/-- Edge color inherited from the suppressed or retained 3DM element. -/
def color (endpoint : ContractedEndpoint) : WireColor :=
  endpoint.edge.color

/-- Whether this is the source end of its stored route. -/
def isSource : ContractedEndpoint → Bool
  | .source _ => true
  | .target _ => false

/-- Direction pointing away from the endpoint vertex along the contracted
route. -/
def outwardDirection
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    ContractedEndpoint → AxisDirection
  | .source edge =>
      AxisDirection.polylineFirstDirection
        (presentation.contractedEdgeRoute edge)
  | .target edge =>
      (AxisDirection.polylineLastDirection
        (presentation.contractedEdgeRoute edge)).opposite

/-- Template side corresponding to the endpoint's outward route direction. -/
def outwardSide
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) : VertexSide :=
  VertexSide.ofDirection (endpoint.outwardDirection presentation)

@[simp]
theorem edge_source (contracted : ContractedEdge) :
    (ContractedEndpoint.source contracted).edge = contracted := by
  rfl

@[simp]
theorem edge_target (contracted : ContractedEdge) :
    (ContractedEndpoint.target contracted).edge = contracted := by
  rfl

end ContractedEndpoint

/-- All edge ends, in contracted-edge order and source-before-target order. -/
def contractedEndpoints (problem : PeriodicThreeDM) :
    List ContractedEndpoint :=
  problem.contractedEdges.flatMap fun edge =>
    [.source edge, .target edge]

/-- Edge-end enumeration has the same prototype-vertex list as the ordinary
graph incidence enumeration. -/
theorem contractedEndpoints_vertices
    (problem : PeriodicThreeDM) :
    problem.contractedEndpoints.map ContractedEndpoint.vertex =
      problem.contractedGraph.incidences := by
  unfold contractedEndpoints contractedGraph PeriodicGraph.incidences
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro edge edgeMember
  simp [PeriodicEdge.incidences, ContractedEndpoint.vertex]

/-- Ends incident to one named prototype vertex. -/
def contractedEndpointsAt (problem : PeriodicThreeDM)
    (vertex : PeriodicThreeDMVertex) : List ContractedEndpoint :=
  problem.contractedEndpoints.filter fun endpoint =>
    endpoint.vertex = vertex

@[simp]
theorem contractedEndpointsAt_mem_iff
    (problem : PeriodicThreeDM) (vertex : PeriodicThreeDMVertex)
    (endpoint : ContractedEndpoint) :
    endpoint ∈ problem.contractedEndpointsAt vertex ↔
      endpoint ∈ problem.contractedEndpoints ∧
        endpoint.vertex = vertex := by
  simp [contractedEndpointsAt]

/-- Every enumerated endpoint owns an emitted contracted edge. -/
theorem ContractedEndpoint.edge_mem_of_mem
    {problem : PeriodicThreeDM} {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    endpoint.edge ∈ problem.contractedEdges := by
  simp only [contractedEndpoints, List.mem_flatMap] at member
  rcases member with ⟨edge, edgeMember, endpointMember⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at endpointMember
  rcases endpointMember with rfl | rfl <;> exact edgeMember

/-- Every enumerated contracted endpoint is based at a listed contracted
vertex. -/
theorem ContractedEndpoint.vertex_mem_of_mem
    {problem : PeriodicThreeDM} {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    endpoint.vertex ∈ problem.contractedGraph.vertices := by
  have edgeMember := endpoint.edge_mem_of_mem member
  have graphEdgeMember :
      endpoint.edge.toPeriodicEdge ∈ problem.contractedGraph.edges := by
    exact List.mem_map.mpr ⟨endpoint.edge, edgeMember, rfl⟩
  have endpoints :=
    (contractedGraph_isWellFormed problem).2 _ graphEdgeMember
  cases endpoint with
  | source edge => exact endpoints.1
  | target edge => exact endpoints.2

/-- Suppression never creates a prototype loop.  For a through edge, the
two original incidence tags are distinct by the global tag-cover theorem. -/
theorem contractedGraph_edgesAreLoopless
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    PeriodicGridDrawing.EdgesAreLoopless problem.contractedGraph := by
  intro graphEdge graphEdgeMember
  simp only [contractedGraph, List.mem_map] at graphEdgeMember
  rcases graphEdgeMember with ⟨edge, edgeMember, rfl⟩
  cases edge with
  | retained color atom incidence =>
      intro equal
      cases equal
  | through color atom first second =>
      have tagsNodup :
          (ContractedEdge.through color atom first second).incidenceTags.Nodup :=
        (List.nodup_flatMap.mp
          (contractedIncidenceTags_nodup problem degree)).1 _ edgeMember
      intro equal
      have indexEqual : first.tripleIndex = second.tripleIndex := by
        injection equal
      simp [ContractedEdge.incidenceTags, ContractedEdge.sourceTag,
        ContractedEdge.targetTag, indexEqual] at tagsNodup

/-- Every contracted route contains a genuine segment. -/
theorem PlanarPresentation.contractedEdgeRoutesHaveSegments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree) :
    PeriodicGridDrawing.EdgeRoutesHaveSegments
      problem.contractedGraph presentation.contractedDrawing :=
  PeriodicGridDrawing.edgeRoutesHaveSegments_of_compatible_of_loopless
    problem.contractedGraph presentation.contractedDrawing
    presentation.contractedDrawing_isCompatible
    (contractedGraph_edgesAreLoopless problem degree)

/-- An emitted edge's named contracted route has at least two points. -/
theorem PlanarPresentation.contractedEdgeRoute_length_ge_two
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    2 ≤ (presentation.contractedEdgeRoute edge).length := by
  rcases List.mem_iff_get.mp member with ⟨edgeIndex, edgeAt⟩
  have taggedMember :
      (edge, edgeIndex.val) ∈ problem.contractedEdges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨edgeIndex.isLt, edgeAt⟩
  let taggedGraphEdge :
      PeriodicEdge PeriodicThreeDMVertex × Nat :=
    (edge.toPeriodicEdge, edgeIndex.val)
  have taggedGraphMember :
      taggedGraphEdge ∈ problem.contractedGraph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    refine ⟨?_, ?_⟩
    · dsimp only [taggedGraphEdge]
      simpa only [contractedGraph, List.length_map] using edgeIndex.isLt
    · simpa [taggedGraphEdge, contractedGraph] using congrArg
        ContractedEdge.toPeriodicEdge edgeAt
  have length := presentation.contractedEdgeRoutesHaveSegments degree
    taggedGraphEdge taggedGraphMember
  rw [presentation.contractedDrawing_edgeRoute taggedMember] at length
  exact length

/-- An emitted edge's contracted route is orthogonal. -/
theorem PlanarPresentation.contractedEdgeRoute_orthogonal_of_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (presentation.contractedEdgeRoute edge) := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, member⟩
  exact presentation.contractedEdgeRoute_orthogonal color atom member

/-- The first direction of a nondegenerate orthogonal polyline is genuine. -/
theorem AxisDirection.polylineFirstDirection_isGenuine_of_orthogonal
    {route : List Cell}
    (length : 2 ≤ route.length)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route) :
    (AxisDirection.polylineFirstDirection route).IsGenuine := by
  rcases route with _ | ⟨first, rest⟩
  · simp at length
  rcases rest with _ | ⟨second, rest⟩
  · simp at length
  exact AxisDirection.between_isGenuine_of_axisAligned
    (List.isChain_cons_cons.mp orthogonal).1

/-- The last direction of a nondegenerate orthogonal polyline is genuine. -/
theorem AxisDirection.polylineLastDirection_isGenuine_of_orthogonal
    {route : List Cell}
    (length : 2 ≤ route.length)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route) :
    (AxisDirection.polylineLastDirection route).IsGenuine := by
  rcases AxisDirection.exists_eq_append_pair_of_length_ge_two length with
    ⟨leading, before, last, rfl⟩
  have finalAligned :
      (GridSegment.mk before last).IsAxisAligned :=
    (List.isChain_append_cons_cons.mp orthogonal).2.1
  unfold AxisDirection.polylineLastDirection
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append]
  change
    (AxisDirection.between last before).opposite.IsGenuine
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned finalAligned)]
  simpa using
    AxisDirection.between_isGenuine_of_axisAligned finalAligned

/-- Every actual contracted endpoint has a genuine outward direction. -/
theorem ContractedEndpoint.outwardDirection_isGenuine
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    (endpoint.outwardDirection presentation).IsGenuine := by
  have edgeMember := endpoint.edge_mem_of_mem member
  have length := presentation.contractedEdgeRoute_length_ge_two
    degree edgeMember
  have orthogonal := presentation.contractedEdgeRoute_orthogonal_of_mem
    edgeMember
  cases endpoint with
  | source edge =>
      exact AxisDirection.polylineFirstDirection_isGenuine_of_orthogonal
        length orthogonal
  | target edge =>
      exact AxisDirection.opposite_isGenuine
        (AxisDirection.polylineLastDirection_isGenuine_of_orthogonal
          length orthogonal)

/-- The side representation exactly embeds back to an actual endpoint's
outward direction. -/
theorem ContractedEndpoint.outwardSide_direction
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    (endpoint.outwardSide presentation).direction =
      endpoint.outwardDirection presentation := by
  exact VertexSide.direction_ofDirection _
    (endpoint.outwardDirection_isGenuine presentation degree member)

end PeriodicThreeDM
end LeanTrominoes
