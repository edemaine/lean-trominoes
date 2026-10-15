/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Data.List.Chain

/-! # Ordered intervals covering a segment form a gap-free chain -/
namespace LeanTrominoes.RationalIntervalPartition

structure Interval where
  start : ℚ
  finish : ℚ
  positive : start < finish
  deriving DecidableEq

def Interval.Contains (interval : Interval) (point : ℚ) : Prop :=
  interval.start ≤ point ∧ point ≤ interval.finish

theorem ordered_cover_chain (pieces : List Interval) (nonempty : pieces ≠ []) (left right : ℚ)
    (positive : left < right) (ordered : pieces.Pairwise (fun first last => first.finish ≤ last.start))
    (bounds : ∀ piece ∈ pieces, left ≤ piece.start ∧ piece.finish ≤ right)
    (cover : ∀ point, left < point → point < right → ∃ piece ∈ pieces, piece.Contains point) :
    pieces.head?.map Interval.start = some left ∧ pieces.getLast?.map Interval.finish = some right ∧
      pieces.IsChain (fun first last => first.finish = last.start) := by
  induction pieces generalizing left with
  | nil => exact (nonempty rfl).elim
  | cons first rest ih =>
    have firstBounds := bounds first (by simp)
    have order := List.pairwise_cons.mp ordered
    have firstStart : first.start = left := by
      apply le_antisymm _ firstBounds.1
      by_contra notBefore
      have before : left < first.start := lt_of_not_ge notBefore
      obtain ⟨piece,member,contains⟩ := cover ((left+first.start)/2) (by linarith) (by linarith [first.positive])
      rcases List.mem_cons.mp member with same | member
      · subst piece
        linarith [contains.1]
      · have after := order.1 piece member
        linarith [contains.1,first.positive]
    refine ⟨by simpa using firstStart,?_⟩
    cases rest with
    | nil =>
      have firstFinish : first.finish = right := by
        apply le_antisymm firstBounds.2
        by_contra notAfter
        have before : first.finish < right := lt_of_not_ge notAfter
        obtain ⟨piece,member,contains⟩ := cover ((first.finish+right)/2) (by linarith [first.positive]) (by linarith)
        have same : piece = first := by simpa using member
        subst piece
        linarith [contains.2]
      refine ⟨?_,?_⟩
      · simpa using firstFinish
      · simp
    | cons next tail =>
      have tailBounds : ∀ piece ∈ next :: tail, first.finish ≤ piece.start ∧ piece.finish ≤ right :=
        fun piece member => ⟨order.1 piece member,(bounds piece (List.mem_cons_of_mem first member)).2⟩
      have nextBounds := tailBounds next (by simp)
      have tailCover : ∀ point, first.finish < point → point < right → ∃ piece ∈ next :: tail, piece.Contains point := by
        intro point after before
        obtain ⟨piece,member,contains⟩ := cover point (by linarith [first.positive]) before
        rcases List.mem_cons.mp member with same | member
        · subst piece
          exact (not_le_of_gt after contains.2).elim
        · exact ⟨piece,member,contains⟩
      have result := ih (by simp) first.finish (by linarith [next.positive]) order.2 tailBounds tailCover
      have joint : next.start = first.finish := by simpa using result.1
      refine ⟨?_,?_⟩
      · simpa only [List.getLast?_cons_cons] using result.2.1
      · exact List.isChain_cons_cons.mpr ⟨joint.symm,result.2.2⟩

end LeanTrominoes.RationalIntervalPartition
