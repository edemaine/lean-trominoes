/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Integral depths for a finite family of nested boundary intervals

An interval's depth counts the intervals it contains. Proper enclosing
intervals receive strictly greater depths, and every depth fits within
the size of the family.
-/
namespace LeanTrominoes.OrthogonalBoundaryRouting

def containedIntervals {α : Type*} [LinearOrder α] (intervals : Finset (α × α))
    (interval : α × α) : Finset (α × α) :=
  intervals.filter fun other => interval.1 ≤ other.1 ∧ other.2 ≤ interval.2

def nestingDepth {α : Type*} [LinearOrder α] (intervals : Finset (α × α))
    (interval : α × α) : Nat := (containedIntervals intervals interval).card

theorem nestingDepth_positive {α : Type*} [LinearOrder α]
    {intervals : Finset (α × α)} {interval : α × α} (member : interval ∈ intervals) :
    0 < nestingDepth intervals interval := by
  apply Finset.card_pos.mpr
  exact ⟨interval,Finset.mem_filter.mpr ⟨member,le_rfl,le_rfl⟩⟩

theorem nestingDepth_le_card {α : Type*} [LinearOrder α]
    (intervals : Finset (α × α)) (interval : α × α) :
    nestingDepth intervals interval ≤ intervals.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem nestingDepth_strict {α : Type*} [LinearOrder α]
    {intervals : Finset (α × α)} {outer inner : α × α}
    (outerMember : outer ∈ intervals)
    (firstOrder : outer.1 < inner.1) (lastOrder : inner.2 < outer.2) :
    nestingDepth intervals inner < nestingDepth intervals outer := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro interval member
    obtain ⟨listed,left,right⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨listed,firstOrder.le.trans left,right.trans lastOrder.le⟩
  · intro equal
    have outerContained : outer ∈ containedIntervals intervals outer :=
      Finset.mem_filter.mpr ⟨outerMember,le_rfl,le_rfl⟩
    rw [← equal] at outerContained
    have impossible := (Finset.mem_filter.mp outerContained).2.1
    exact (not_le_of_gt firstOrder) impossible

end LeanTrominoes.OrthogonalBoundaryRouting
