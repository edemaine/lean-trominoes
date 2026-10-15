/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceIntervalSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalIntervalSortedPartition
import Mathlib.Data.List.Dedup

/-! # Sorting the executable piece list gives an exact partition from source to target -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntervalPartition

def edgeRoutePieceInterval (piece : EdgeRoutePiece) : Interval :=
  if positive : piece.start < piece.finish then ⟨piece.start,piece.finish,positive⟩ else ⟨0,1,by norm_num⟩

theorem edgeRoutePieceInterval_fields {piece : EdgeRoutePiece} (positive : piece.start < piece.finish) :
    (edgeRoutePieceInterval piece).start = piece.start ∧ (edgeRoutePieceInterval piece).finish = piece.finish := by
  simp [edgeRoutePieceInterval,positive]

private theorem map_interval_order (pieces : List EdgeRoutePiece)
    (positive : ∀ piece ∈ pieces, piece.start < piece.finish)
    (ordered : pieces.Pairwise (fun first last => first.finish ≤ last.start)) :
    (pieces.map edgeRoutePieceInterval).Pairwise (fun first last => first.finish ≤ last.start) := by
  induction pieces with
  | nil => simp
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (fun piece member => positive piece (List.mem_cons_of_mem first member)) order.2⟩
    intro last member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    rw [(edgeRoutePieceInterval_fields (positive first (by simp))).2,
      (edgeRoutePieceInterval_fields (positive piece (List.mem_cons_of_mem first pieceMember))).1]
    exact order.1 piece pieceMember

theorem edgeRoutePieces_ordered_cover_chain (pieces : List EdgeRoutePiece) (nonempty : pieces ≠ []) (left right : ℚ)
    (rangePositive : left < right) (positive : ∀ piece ∈ pieces, piece.start < piece.finish)
    (ordered : pieces.Pairwise (fun first last => first.finish ≤ last.start))
    (bounds : ∀ piece ∈ pieces, left ≤ piece.start ∧ piece.finish ≤ right)
    (cover : ∀ parameter, left < parameter → parameter < right → ∃ piece ∈ pieces, piece.start ≤ parameter ∧ parameter ≤ piece.finish) :
    pieces.head?.map EdgeRoutePiece.start = some left ∧ pieces.getLast?.map EdgeRoutePiece.finish = some right ∧
      pieces.IsChain (fun first last => first.finish = last.start) := by
  have mappedBounds : ∀ interval ∈ pieces.map edgeRoutePieceInterval, left ≤ interval.start ∧ interval.finish ≤ right := by
    intro interval member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    rw [(edgeRoutePieceInterval_fields (positive piece pieceMember)).1,(edgeRoutePieceInterval_fields (positive piece pieceMember)).2]
    exact bounds piece pieceMember
  have mappedCover : ∀ parameter, left < parameter → parameter < right → ∃ interval ∈ pieces.map edgeRoutePieceInterval, interval.Contains parameter := by
    intro parameter after before
    obtain ⟨piece,pieceMember,contains⟩ := cover parameter after before
    refine ⟨edgeRoutePieceInterval piece,List.mem_map.mpr ⟨piece,pieceMember,rfl⟩,?_⟩
    unfold Interval.Contains
    rw [(edgeRoutePieceInterval_fields (positive piece pieceMember)).1,(edgeRoutePieceInterval_fields (positive piece pieceMember)).2]
    exact contains
  have partition := ordered_cover_chain (pieces.map edgeRoutePieceInterval) (by simpa using nonempty) left right rangePositive
    (map_interval_order pieces positive ordered) mappedBounds mappedCover
  have starts : pieces.map (fun piece => (edgeRoutePieceInterval piece).start) = pieces.map EdgeRoutePiece.start := by
    apply List.map_congr_left
    exact fun piece member => (edgeRoutePieceInterval_fields (positive piece member)).1
  have finishes : pieces.map (fun piece => (edgeRoutePieceInterval piece).finish) = pieces.map EdgeRoutePiece.finish := by
    apply List.map_congr_left
    exact fun piece member => (edgeRoutePieceInterval_fields (positive piece member)).2
  have head := partition.1
  have last := partition.2.1
  rw [← List.head?_map,List.map_map] at head
  change (pieces.map (fun piece => (edgeRoutePieceInterval piece).start)).head? = some left at head
  rw [starts,List.head?_map] at head
  rw [← List.getLast?_map,List.map_map] at last
  change (pieces.map (fun piece => (edgeRoutePieceInterval piece).finish)).getLast? = some right at last
  rw [finishes,List.getLast?_map] at last
  refine ⟨head,last,?_⟩
  have chain := (List.isChain_map edgeRoutePieceInterval).mp partition.2.2
  exact chain.imp_of_mem_imp (fun first last fm lm equal => by
    simpa only [(edgeRoutePieceInterval_fields (positive first fm)).2,(edgeRoutePieceInterval_fields (positive last lm)).1] using equal)

theorem edgeRoutePiece_finish_le_start {first last : EdgeRoutePiece}
    (_firstPositive : first.start < first.finish) (lastPositive : last.start < last.finish)
    (ordered : first.start ≤ last.start) (disjoint : first.InteriorsDisjoint last) : first.finish ≤ last.start := by
  by_contra notBefore
  have overlap : last.start < first.finish := lt_of_not_ge notBefore
  have room : last.start < min first.finish last.finish := lt_min overlap lastPositive
  apply disjoint ((last.start+min first.finish last.finish)/2)
  · linarith
  · linarith [min_le_left first.finish last.finish]
  · linarith
  · linarith [min_le_right first.finish last.finish]

theorem edgeRoutePieces_finish_order (pieces : List EdgeRoutePiece) (nodup : pieces.Nodup)
    (positive : ∀ piece ∈ pieces, piece.start < piece.finish)
    (ordered : pieces.Pairwise (fun first last => first.start ≤ last.start))
    (disjoint : ∀ first ∈ pieces, ∀ last ∈ pieces, first ≠ last → first.InteriorsDisjoint last) :
    pieces.Pairwise (fun first last => first.finish ≤ last.start) := by
  induction pieces with
  | nil => simp
  | cons first rest ih =>
    have unique := List.nodup_cons.mp nodup
    have order := List.pairwise_cons.mp ordered
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih unique.2 (fun piece member => positive piece (List.mem_cons_of_mem first member)) order.2
      (fun a am b bm different => disjoint a (List.mem_cons_of_mem first am) b (List.mem_cons_of_mem first bm) different)⟩
    intro last member
    exact edgeRoutePiece_finish_le_start (positive first (by simp)) (positive last (List.mem_cons_of_mem first member))
      (order.1 last member) (disjoint first (by simp) last (List.mem_cons_of_mem first member)
        (fun equal => unique.1 (by simpa only [equal] using member)))

def sortEdgeRoutePieces (pieces : List EdgeRoutePiece) : List EdgeRoutePiece :=
  pieces.dedup.mergeSort (fun first last => decide (first.start ≤ last.start))

theorem sortEdgeRoutePieces_mem_iff {pieces : List EdgeRoutePiece} {piece : EdgeRoutePiece} :
    piece ∈ sortEdgeRoutePieces pieces ↔ piece ∈ pieces := by
  have perm : (sortEdgeRoutePieces pieces).Perm pieces.dedup := List.mergeSort_perm ..
  exact perm.mem_iff.trans (by simp)

theorem sortEdgeRoutePieces_nodup (pieces : List EdgeRoutePiece) : (sortEdgeRoutePieces pieces).Nodup := by
  have perm : (sortEdgeRoutePieces pieces).Perm pieces.dedup := List.mergeSort_perm ..
  exact perm.nodup_iff.mpr (List.nodup_dedup pieces)

theorem sortEdgeRoutePieces_start_order (pieces : List EdgeRoutePiece) :
    (sortEdgeRoutePieces pieces).Pairwise (fun first last => first.start ≤ last.start) := by
  have order := List.pairwise_mergeSort (le := fun first last : EdgeRoutePiece => decide (first.start ≤ last.start))
    (by intro first middle last fm ml; simp only [decide_eq_true_eq] at *; exact le_trans fm ml)
    (by intro first last; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _) pieces.dedup
  simpa only [sortEdgeRoutePieces,decide_eq_true_eq] using order

theorem nonverticalEdgePieces_sorted_partition {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).head?.map EdgeRoutePiece.start = some 0 ∧
      (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).getLast?.map EdgeRoutePiece.finish = some 1 ∧
      (sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).IsChain (fun first last => first.finish = last.start) := by
  let pieces := nonverticalEdgePieces graph drawing tagged
  let sorted := sortEdgeRoutePieces pieces
  have positive : ∀ piece ∈ sorted, piece.start < piece.finish := fun piece member =>
    (nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical (sortEdgeRoutePieces_mem_iff.mp member)).2.1
  have disjoint : ∀ first ∈ sorted, ∀ last ∈ sorted, first ≠ last → first.InteriorsDisjoint last := fun first fm last lm different =>
    nonverticalEdgePieces_interiors_disjoint planar graphLocal straight tagged nonvertical
      (sortEdgeRoutePieces_mem_iff.mp fm) (sortEdgeRoutePieces_mem_iff.mp lm) different
  have cover : ∀ parameter, (0 : ℚ) < parameter → parameter < 1 → ∃ piece ∈ sorted, piece.start ≤ parameter ∧ parameter ≤ piece.finish := by
    intro parameter after before
    obtain ⟨piece,pieceMember,contains⟩ := nonverticalEdgePieces_cover planar graphLocal straight member nonvertical parameter after.le before.le
    exact ⟨piece,sortEdgeRoutePieces_mem_iff.mpr pieceMember,contains⟩
  have nonempty : sorted ≠ [] := by
    intro empty
    obtain ⟨piece,pieceMember,_⟩ := cover (1/2) (by norm_num) (by norm_num)
    simp [empty] at pieceMember
  apply edgeRoutePieces_ordered_cover_chain sorted nonempty 0 1 (by norm_num) positive
    (edgeRoutePieces_finish_order sorted (sortEdgeRoutePieces_nodup pieces) positive (sortEdgeRoutePieces_start_order pieces) disjoint)
  · intro piece pieceMember
    have bounds := nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical (sortEdgeRoutePieces_mem_iff.mp pieceMember)
    exact ⟨bounds.1,bounds.2.2⟩
  · exact cover

end LeanTrominoes.PeriodicGridDrawing
