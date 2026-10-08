/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalIntervalPartition

/-! # Disjoint interval interiors turn endpoint order into partition order -/
namespace LeanTrominoes.RationalIntervalPartition

def Interval.InteriorsDisjoint (first last : Interval) : Prop :=
  ∀ point : ℚ, first.start < point → point < first.finish → last.start < point → point < last.finish → False

theorem finish_le_start_of_disjoint {first last : Interval} (ordered : first.start ≤ last.start)
    (disjoint : first.InteriorsDisjoint last) : first.finish ≤ last.start := by
  by_contra notBefore
  have overlap : last.start < first.finish := lt_of_not_ge notBefore
  have room : last.start < min first.finish last.finish := lt_min overlap last.positive
  apply disjoint ((last.start+min first.finish last.finish)/2)
  · linarith
  · linarith [min_le_left first.finish last.finish]
  · linarith
  · linarith [min_le_right first.finish last.finish]

theorem pairwise_partition_order {pieces : List Interval}
    (ordered : pieces.Pairwise (fun first last => first.start ≤ last.start))
    (disjoint : pieces.Pairwise Interval.InteriorsDisjoint) :
    pieces.Pairwise (fun first last => first.finish ≤ last.start) := by
  induction pieces with
  | nil => simp
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    have separation := List.pairwise_cons.mp disjoint
    exact List.pairwise_cons.mpr ⟨fun last member => finish_le_start_of_disjoint (order.1 last member) (separation.1 last member),ih order.2 separation.2⟩

theorem disjoint_ordered_cover_chain (pieces : List Interval) (nonempty : pieces ≠ []) (left right : ℚ)
    (positive : left < right) (ordered : pieces.Pairwise (fun first last => first.start ≤ last.start))
    (disjoint : pieces.Pairwise Interval.InteriorsDisjoint)
    (bounds : ∀ piece ∈ pieces, left ≤ piece.start ∧ piece.finish ≤ right)
    (cover : ∀ point, left < point → point < right → ∃ piece ∈ pieces, piece.Contains point) :
    pieces.head?.map Interval.start = some left ∧ pieces.getLast?.map Interval.finish = some right ∧
      pieces.IsChain (fun first last => first.finish = last.start) :=
  ordered_cover_chain pieces nonempty left right positive (pairwise_partition_order ordered disjoint) bounds cover

end LeanTrominoes.RationalIntervalPartition
