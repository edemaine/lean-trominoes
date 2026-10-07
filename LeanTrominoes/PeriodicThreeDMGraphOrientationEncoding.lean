/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMContractedEdgeOrientation
import LeanTrominoes.TrichromaticGraphOrientation

/-! # Dense vertex and edge names for contracted 3DM graphs -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget
namespace GraphOrientationEncoding
open TrichromaticGraphOrientation
set_option maxHeartbeats 800000

def vertexKind : PeriodicThreeDMVertex → Bool
  | .triple _ => true
  | .element _ _ => false

def edgeRecord (problem : PeriodicThreeDM) (edge : ContractedEdge) :
    PeriodicEdge Nat × WireColor :=
  (⟨problem.contractedGraph.vertices.idxOf edge.toPeriodicEdge.source,
    problem.contractedGraph.vertices.idxOf edge.toPeriodicEdge.target,
    edge.toPeriodicEdge.offset⟩,edge.color)

def input (problem : PeriodicThreeDM) : Input :=
  (problem.contractedGraph.vertices.map vertexKind,problem.contractedEdges.map (edgeRecord problem))

def endpointLiteral (problem : PeriodicThreeDM) : ContractedEndpoint → PeriodicLiteral Nat
  | .source edge => ⟨problem.contractedEdges.idxOf edge,(0,0),false⟩
  | .target edge => ⟨problem.contractedEdges.idxOf edge,
      Cell.sub (0,0) edge.toPeriodicEdge.offset,true⟩

def endpointRecord (problem : PeriodicThreeDM) (endpoint : ContractedEndpoint) : End :=
  (problem.contractedGraph.vertices.idxOf endpoint.vertex,
    endpointLiteral problem endpoint,endpoint.color)

private theorem indexed_edge (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge} {index : Nat} (member : (edge,index) ∈ problem.contractedEdges.zipIdx) :
    problem.contractedEdges.idxOf edge = index := by
  have data := List.mem_zipIdx' member
  rw [data.2]
  exact (contractedEdges_nodup problem degree).idxOf_getElem index data.1

theorem ends_eq (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree) :
    ends (input problem) = problem.contractedEndpoints.map (endpointRecord problem) := by
  unfold ends input
  simp only [List.zipIdx_map,List.flatMap_map]
  calc
    _ = problem.contractedEdges.zipIdx.flatMap (fun t =>
        [ContractedEndpoint.source t.1,ContractedEndpoint.target t.1].map (endpointRecord problem)) := by
      apply List.flatMap_congr
      intro tagged member
      dsimp only [Prod.map,id]
      rw [← indexed_edge problem degree member]
      rfl
    _ = _ := by
      rw [contractedEndpoints,List.map_flatMap]
      conv_rhs => rw [← List.zipIdx_map_fst 0 problem.contractedEdges,List.flatMap_map]

theorem endsAt_eq (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (vertex : PeriodicThreeDMVertex) :
    endsAt (input problem) (problem.contractedGraph.vertices.idxOf vertex) =
      (problem.contractedEndpointsAt vertex).map (endpointRecord problem) := by
  rw [endsAt,ends_eq problem degree,contractedEndpointsAt,List.filter_map]
  apply congrArg (List.map (endpointRecord problem))
  apply List.filter_congr
  intro endpoint member
  have vertexMember := endpoint.vertex_mem_of_mem member
  by_cases equal : endpoint.vertex = vertex
  · simp [endpointRecord,equal]
  · have different : problem.contractedGraph.vertices.idxOf endpoint.vertex ≠
        problem.contractedGraph.vertices.idxOf vertex := fun h =>
      equal ((List.idxOf_inj vertexMember).mp h)
    simp [endpointRecord,equal,different]

theorem incoming_eq (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (vertex : PeriodicThreeDMVertex) :
    incoming (input problem) (problem.contractedGraph.vertices.idxOf vertex) =
      (problem.contractedEndpointsAt vertex).map (endpointLiteral problem) := by
  rw [incoming,endsAt_eq problem degree vertex,List.map_map]
  rfl

theorem colors_eq (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (vertex : PeriodicThreeDMVertex) :
    colors (input problem) (problem.contractedGraph.vertices.idxOf vertex) =
      (problem.contractedEndpointsAt vertex).map ContractedEndpoint.color := by
  rw [colors,endsAt_eq problem degree vertex,List.map_map]
  rfl

def edgeAssignment (problem : PeriodicThreeDM) (a : Nat → Cell → Bool) :
    ContractedEdgeOrientation := fun edge => a (problem.contractedEdges.idxOf edge)

theorem literalValue_eq (problem : PeriodicThreeDM) (a : Nat → Cell → Bool)
    (cell : Cell) (endpoint : ContractedEndpoint) :
    (a (endpointLiteral problem endpoint).atom
      (Cell.add cell (endpointLiteral problem endpoint).offset) ==
        (endpointLiteral problem endpoint).value) =
      endpoint.edgeInward (edgeAssignment problem a) cell := by
  cases endpoint with
  | source edge =>
      have zero : Cell.add cell (0,0) = cell := by rcases cell with ⟨x,y⟩; simp [Cell.add]
      simp only [endpointLiteral,zero,ContractedEndpoint.edgeInward,edgeAssignment]
      cases a (problem.contractedEdges.idxOf edge) cell <;> rfl
  | target edge =>
      simp only [endpointLiteral,ContractedEndpoint.edgeInward,edgeAssignment]
      have cells : Cell.add cell (Cell.sub (0,0) edge.toPeriodicEdge.offset) =
          Cell.sub cell edge.toPeriodicEdge.offset := by
        rcases cell with ⟨x,y⟩; rcases edge.toPeriodicEdge.offset with ⟨dx,dy⟩
        simp [Cell.add,Cell.sub,sub_eq_add_neg]
      rw [cells]
      cases a (problem.contractedEdges.idxOf edge) (Cell.sub cell edge.toPeriodicEdge.offset) <;> rfl

theorem clauseValues_eq (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (a : Nat → Cell → Bool) (cell : Cell) (vertex : PeriodicThreeDMVertex) :
    PeriodicOneInThree.clauseValues a cell
      (incoming (input problem) (problem.contractedGraph.vertices.idxOf vertex)) =
      (problem.contractedEndpointsAt vertex).map
        (fun endpoint => endpoint.edgeInward (edgeAssignment problem a) cell) := by
  rw [incoming_eq problem degree,PeriodicOneInThree.clauseValues,List.map_map]
  apply List.map_congr_left
  intro endpoint _
  exact literalValue_eq problem a cell endpoint

end GraphOrientationEncoding
end LeanTrominoes.PeriodicThreeDM
