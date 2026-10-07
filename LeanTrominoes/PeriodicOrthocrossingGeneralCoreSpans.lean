/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreClassification
import LeanTrominoes.GridSegmentRealPeriodicSeparation

/-! # Every track piece is strictly shorter than one period -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem core_segment_spans {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    ∀ piece ∈ classifiedCore graph tagged.1 tagged.2,
      |piece.segment.finish.1-piece.segment.start.1| < (drawingGridSize graph : Int) ∧
        |piece.segment.finish.2-piece.segment.start.2| < (drawingGridSize graph : Int) := by
  have sourceBounds := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have targetBounds := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have tracks := edgeTrack_bounds graph member
  have indexBound : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have positive : (1 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  have gatePositive : (0 : Int) < 3*graph.vertices.length+2*graph.edges.length+4+2*tagged.2 := by omega
  have gateBound : (3*graph.vertices.length+2*graph.edges.length+4+2*tagged.2 : Int) < drawingGridSize graph := by
    unfold drawingGridSize
    omega
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  · simp [classifiedCore,offset,Cell.add,Cell.scale,abs_lt]
    omega
  · by_cases order : portX graph (targetPort tagged.1 tagged.2) < portX graph (sourcePort tagged.1 tagged.2)
    all_goals simp [classifiedCore,offset,order,Cell.add,Cell.scale,abs_lt]; omega
  · by_cases order : portX graph (sourcePort tagged.1 tagged.2) < portX graph (targetPort tagged.1 tagged.2)
    all_goals simp [classifiedCore,offset,order,Cell.add,Cell.scale,abs_lt]; omega
  · simp [classifiedCore,offset,Cell.add,Cell.scale,abs_lt]
    omega
  · simp [classifiedCore,offset,Cell.add,Cell.scale,abs_lt]
    omega

private theorem width_eq_abs (first last : Int) : max first last-min first last = |last-first| := by
  rcases le_total first last with forward | backward
  · rw [max_eq_right forward,min_eq_left forward,abs_of_nonneg (by omega)]
  · rw [max_eq_left backward,min_eq_right backward,abs_of_nonpos (by omega)]
    omega

theorem core_piece_copies_disjoint {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains point)
    (secondContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) secondCell)).RealContains point) :
    firstCell = secondCell := by
  have spans := core_segment_spans wellFormed member edgeLocal piece pieceMember
  apply GridSegment.real_translated_copies_disjoint (by exact_mod_cast drawingGridSize_pos graph) ?_ ?_
    firstContains secondContains
  · simpa only [width_eq_abs] using spans.1
  · simpa only [width_eq_abs] using spans.2

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
