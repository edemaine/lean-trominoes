/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceJoins
import LeanTrominoes.GridPolylineRouteWordOrthogonal

/-! # The executable nonvertical replacement route is orthogonal and has the exact piece image -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem nonverticalEdgeRoute_orthogonal_image {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    OrthogonalPolyline (nonverticalEdgeRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (nonverticalEdgeRoute graph drawing tagged) point ↔
        ∃ piece ∈ nonverticalEdgePieces graph drawing tagged, GridPolyline.RealContains piece.route point := by
  have partition := nonverticalEdgePieces_sorted_partition planar degree graphLocal straight member nonvertical
  have chain : ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route).IsChain
      (fun first last => first.getLast? = last.head?) := by
    apply (List.isChain_map EdgeRoutePiece.route).mpr
    exact partition.2.2.imp_of_mem_imp (fun first last fm lm equal =>
      nonverticalEdgePieces_join planar degree graphLocal straight member nonvertical
        (sortEdgeRoutePieces_mem_iff.mp fm) (sortEdgeRoutePieces_mem_iff.mp lm) equal)
  have long : ∀ route ∈ (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route,
      2 ≤ route.length := by
    intro route routeMember
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp routeMember
    exact (nonverticalEdgePieces_route_valid planar degree graphLocal straight tagged (sortEdgeRoutePieces_mem_iff.mp pieceMember)).1.1
  have orthogonal : ∀ route ∈ (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route,
      OrthogonalPolyline route := by
    intro route routeMember
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp routeMember
    exact (nonverticalEdgePieces_route_valid planar degree graphLocal straight tagged (sortEdgeRoutePieces_mem_iff.mp pieceMember)).2
  cases sorted : sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged) with
  | nil => simp [sorted] at partition
  | cons first rest =>
    rw [sorted] at long orthogonal chain
    have valid := GridPolyline.joinWord_orthogonal_image long orthogonal chain
    unfold nonverticalEdgeRoute
    rw [sorted]
    simp only [List.map_cons]
    refine ⟨valid.1,?_⟩
    intro point
    rw [valid.2]
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
