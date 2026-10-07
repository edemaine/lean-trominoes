/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCorrectness
import LeanTrominoes.OrthogonalPolylineSymmetries

/-! # Orthogonality of the general maximum-degree-four construction -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem portX_lt_gridSize {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    0 < portX graph port ∧ portX graph port < drawingGridSize graph := by
  have bounds := portX_bounds wellFormed member
  unfold drawingGridSize
  omega

theorem sourcePortX_ne_targetPortX {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) :
    portX graph (sourcePort tagged.1 tagged.2) ≠ portX graph (targetPort tagged.1 tagged.2) := by
  intro equal
  have same := portX_injective wellFormed (sourcePort_mem_allPorts graph member)
    (targetPort_mem_allPorts graph member) equal
  have kinds := congrArg GraphPort.endKind same
  cases kinds

@[simp] theorem core_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (index : Nat) :
    (core graph edge index).head? = some (portX graph (sourcePort edge index),3) := by
  unfold core
  split <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem core_last {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (index : Nat) :
    (core graph edge index).getLast? = some (Cell.add (portX graph (targetPort edge index),3)
      (Cell.scale (drawingGridSize graph : Int) edge.offset)) := by
  unfold core
  split <;> simp_all
  all_goals split <;> simp_all

theorem core_length {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (index : Nat) : 2 ≤ (core graph edge index).length := by
  unfold core
  split <;> simp_all
  all_goals split <;> simp_all

theorem core_orthogonal {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    OrthogonalPolyline (core graph tagged.1 tagged.2) := by
  have sourceMember := sourcePort_mem_allPorts graph member
  have targetMember := targetPort_mem_allPorts graph member
  have sourceBounds := portX_lt_gridSize wellFormed sourceMember
  have targetBounds := portX_lt_gridSize wellFormed targetMember
  have sourceBeforeGate := portX_bounds wellFormed sourceMember
  have targetBeforeGate := portX_bounds wellFormed targetMember
  have tracks := edgeTrack_bounds graph member
  have indexBound : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have different := sourcePortX_ne_targetPortX wellFormed member
  have positive := drawingGridSize_pos graph
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  · simp [core,offset,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,Cell.add,Cell.scale] <;> omega
  · by_cases order : portX graph (targetPort tagged.1 tagged.2) < portX graph (sourcePort tagged.1 tagged.2)
    all_goals simp [core,offset,order,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,Cell.add,Cell.scale] <;> omega
  · by_cases order : portX graph (sourcePort tagged.1 tagged.2) < portX graph (targetPort tagged.1 tagged.2)
    all_goals simp [core,offset,order,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,Cell.add,Cell.scale] <;> omega
  · simp [core,offset,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,Cell.add,Cell.scale,drawingGridSize] at * <;> omega
  · simp [core,offset,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,Cell.add,Cell.scale,drawingGridSize] at * <;> omega

theorem fan_orthogonal {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (port : GraphPort Vertex) : OrthogonalPolyline (fan graph true port) := by
  let rank : Fin 4 := ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩
  have original : OrthogonalPolyline (degreeFourFan rank) :=
    (orthogonalPolyline_iff_segments _).mpr (degreeFourFan_orthogonal rank)
  exact original.translate (vertexX graph port.vertex,0)

theorem route_orthogonal {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) : OrthogonalPolyline (route graph true tagged.1 tagged.2) := by
  have sourceMember := sourcePort_mem_allPorts graph member
  have targetMember := targetPort_mem_allPorts graph member
  have source := fan_orthogonal graph (sourcePort tagged.1 tagged.2)
  have middle := core_orthogonal wellFormed member edgeLocal
  have target := (fan_orthogonal graph (targetPort tagged.1 tagged.2)).reverse.translate
    (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
  have sourceBoundary : (fan graph true (sourcePort tagged.1 tagged.2)).getLast? =
      (core graph tagged.1 tagged.2).head? := by
    rw [core_head,fan_last true sourceMember (fun _ => degree)]
  have targetBoundary : (core graph tagged.1 tagged.2).getLast? =
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph true (targetPort tagged.1 tagged.2)).reverse).head? := by
    rw [core_last,translatePolyline,List.head?_map,List.head?_reverse,
      fan_last true targetMember (fun _ => degree)]
    simp [Cell.add,add_comm]
  unfold route
  apply isChain_joinPolylines
  · exact isChain_joinPolylines source middle sourceBoundary
  · exact target
  · rw [joinPolylines_getLast?_of_second (core_length graph tagged.1 tagged.2)]
    exact targetBoundary

attribute [local irreducible] fan core route drawing

theorem drawing_isOrthogonal {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 4) (isLocal : graph.IsLocal) :
    (drawing graph true).IsOrthogonal := by
  apply (PeriodicGridDrawing.isOrthogonal_iff_routes _).mpr
  intro points member
  unfold drawing at member
  change points ∈ graph.edges.zipIdx.map (fun tagged => route graph true tagged.1 tagged.2) at member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact route_orthogonal wellFormed degree taggedMember (isLocal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
