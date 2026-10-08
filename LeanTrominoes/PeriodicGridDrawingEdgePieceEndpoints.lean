/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceIntervals

/-! # Exact graph endpoints and boundary ports of the enumerated pieces -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem sourceEdgePiece_head {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) :
    (sourceEdgePiece graph drawing tagged).route.head? =
      some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source)) :=
  paddedIncidenceRoute_head ..

theorem sourceEdgePiece_last {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    (sourceEdgePiece graph drawing tagged).route.getLast? =
      some (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source))
        (Cell.scale (crossingBound drawing.gridSize) (portBoundaryAnchor graph drawing (sourcePort tagged.1 tagged.2)))) :=
  paddedIncidenceRoute_last (distinctPortRayKeys_of_planar_straight planar straight) degree (sourcePort_mem_allPorts graph member)

theorem targetEdgePiece_last {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) :
    (targetEdgePiece graph drawing tagged).route.getLast? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))) := by
  change (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse.getLast? = _
  rw [List.getLast?_reverse,liftedPaddedIncidenceRoute_eq_translate]
  simp only [translatePolyline,List.head?_map,paddedIncidenceRoute_head,Option.map_some,targetPort]

theorem targetEdgePiece_head {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    (targetEdgePiece graph drawing tagged).route.head? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))
          (Cell.scale (crossingBound drawing.gridSize) (portBoundaryAnchor graph drawing (targetPort tagged.1 tagged.2))))) := by
  change (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse.head? = _
  rw [List.head?_reverse,liftedPaddedIncidenceRoute_eq_translate]
  simp only [translatePolyline,List.getLast?_map]
  rw [paddedIncidenceRoute_last (distinctPortRayKeys_of_planar_straight planar straight) degree (targetPort_mem_allPorts graph member)]
  rfl

theorem nonverticalEdgePieces_source_match {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {piece : EdgeRoutePiece} (member : piece ∈ nonverticalEdgePieces graph drawing tagged) (start : piece.start = 0) :
    piece.route.head? = some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source)) := by
  have fan := edgeFanParameter_bounds planar straight tagged.2 nonvertical
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((source | rectangle) | crossing) | target
  · subst piece
    exact sourceEdgePiece_head ..
  · have positive := (rectangleEdgePieces_valid planar degree graphLocal straight tagged.2 rectangle).1
    exact (ne_of_gt positive start).elim
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst piece
    have positive := (crossingEdgePiece_interval_bounds planar straight tagged.2 line crosses).1
    exact (ne_of_gt positive start).elim
  · subst piece
    change 1-edgeFanParameter graph drawing tagged.2 = 0 at start
    linarith

theorem nonverticalEdgePieces_target_match {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {piece : EdgeRoutePiece} (member : piece ∈ nonverticalEdgePieces graph drawing tagged) (finish : piece.finish = 1) :
    piece.route.getLast? = some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
      (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))) := by
  have fan := edgeFanParameter_bounds planar straight tagged.2 nonvertical
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((source | rectangle) | crossing) | target
  · subst piece
    change edgeFanParameter graph drawing tagged.2 = 1 at finish
    linarith
  · have before := (rectangleEdgePieces_valid planar degree graphLocal straight tagged.2 rectangle).2.2.1
    exact (ne_of_lt before finish).elim
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst piece
    have before := (crossingEdgePiece_interval_bounds planar straight tagged.2 line crosses).2.2
    exact (ne_of_lt before finish).elim
  · subst piece
    exact targetEdgePiece_last ..

end LeanTrominoes.PeriodicGridDrawing
