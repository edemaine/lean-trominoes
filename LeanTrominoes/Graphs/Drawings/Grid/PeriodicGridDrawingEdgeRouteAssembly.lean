/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePiecePartition
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEndpoints
import LeanTrominoes.Common.Geometry.GridPolylineRouteWordEndpoints

/-! # Executable source-to-target assembly of the actual replacement pieces -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def nonverticalEdgeRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) : List Cell :=
  GridPolyline.joinWord ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route)

theorem nonverticalEdgeRoute_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    2 ≤ (nonverticalEdgeRoute graph drawing tagged).length ∧
      (nonverticalEdgeRoute graph drawing tagged).head? =
        some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source)) ∧
      (nonverticalEdgeRoute graph drawing tagged).getLast? =
        some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
          (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))) := by
  have partition := nonverticalEdgePieces_sorted_partition planar degree graphLocal straight member nonvertical
  have long : ∀ route ∈ (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route, 2 ≤ route.length := by
    intro route member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    exact (nonverticalEdgePieces_route_valid planar degree graphLocal straight tagged (sortEdgeRoutePieces_mem_iff.mp pieceMember)).1.1
  cases sorted : sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged) with
  | nil => simp [sorted] at partition
  | cons first rest =>
    rw [sorted] at partition long
    have endpoints := GridPolyline.joinWord_endpoints long
    have firstMember : first ∈ nonverticalEdgePieces graph drawing tagged := sortEdgeRoutePieces_mem_iff.mp (by simp [sorted])
    have firstStart : first.start = 0 := by simpa using partition.1
    unfold nonverticalEdgeRoute
    rw [sorted]
    simp only [List.map_cons]
    refine ⟨endpoints.1,endpoints.2.1.trans (nonverticalEdgePieces_source_match planar degree graphLocal straight tagged nonvertical firstMember firstStart),?_⟩
    rw [endpoints.2.2]
    change ((first :: rest).map EdgeRoutePiece.route).getLast?.bind List.getLast? = _
    rw [List.getLast?_map]
    cases last : (first :: rest).getLast? with
    | none => simp [last] at partition
    | some piece =>
      have pieceMember : piece ∈ nonverticalEdgePieces graph drawing tagged :=
        sortEdgeRoutePieces_mem_iff.mp (by rw [sorted]; exact List.mem_of_mem_getLast? (by simp [last]))
      have finish : piece.finish = 1 := by simpa [last] using partition.2.1
      simp only [Option.map_some,Option.bind_some]
      exact nonverticalEdgePieces_target_match planar degree graphLocal straight tagged nonvertical pieceMember finish

theorem nonverticalEdgeRoute_valid_of_joins {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (joins : ∀ first ∈ nonverticalEdgePieces graph drawing tagged, ∀ last ∈ nonverticalEdgePieces graph drawing tagged,
      first.finish = last.start → first.route.getLast? = last.route.head?)
    (separated : GridPolyline.SeparatedWord ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route)) :
    GridPolyline.IsRealOpenSimple (nonverticalEdgeRoute graph drawing tagged) ∧
      OrthogonalPolyline (nonverticalEdgeRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (nonverticalEdgeRoute graph drawing tagged) point ↔
        ∃ piece ∈ nonverticalEdgePieces graph drawing tagged, GridPolyline.RealContains piece.route point := by
  have partition := nonverticalEdgePieces_sorted_partition planar degree graphLocal straight member nonvertical
  have chain : ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route).IsChain
      (fun first last => first.getLast? = last.head?) := by
    apply (List.isChain_map EdgeRoutePiece.route).mpr
    exact partition.2.2.imp_of_mem_imp (fun first last fm lm equal => joins first (sortEdgeRoutePieces_mem_iff.mp fm)
      last (sortEdgeRoutePieces_mem_iff.mp lm) equal)
  have simple : ∀ route ∈ (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route,
      GridPolyline.IsRealOpenSimple route := by
    intro route member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    exact (nonverticalEdgePieces_route_valid planar degree graphLocal straight tagged (sortEdgeRoutePieces_mem_iff.mp pieceMember)).1
  have orthogonal : ∀ route ∈ (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route,
      OrthogonalPolyline route := by
    intro route member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    exact (nonverticalEdgePieces_route_valid planar degree graphLocal straight tagged (sortEdgeRoutePieces_mem_iff.mp pieceMember)).2
  cases sorted : sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged) with
  | nil => simp [sorted] at partition
  | cons first rest =>
    rw [sorted] at simple orthogonal chain separated
    have valid := GridPolyline.joinWord_valid simple orthogonal chain separated
    unfold nonverticalEdgeRoute
    rw [sorted]
    simp only [List.map_cons]
    refine ⟨valid.1,valid.2.1,?_⟩
    intro point
    rw [valid.2.2.2.2]
    constructor
    · rintro ⟨route,routeMember,contains⟩
      change route ∈ (first :: rest).map EdgeRoutePiece.route at routeMember
      obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp routeMember
      exact ⟨piece,sortEdgeRoutePieces_mem_iff.mp (by rw [sorted]; exact pieceMember),contains⟩
    · rintro ⟨piece,pieceMember,contains⟩
      change ∃ route ∈ (first :: rest).map EdgeRoutePiece.route, GridPolyline.RealContains route point
      refine ⟨piece.route,List.mem_map.mpr ⟨piece,?_,rfl⟩,contains⟩
      rw [← sorted]
      exact sortEdgeRoutePieces_mem_iff.mpr pieceMember

end LeanTrominoes.PeriodicGridDrawing
