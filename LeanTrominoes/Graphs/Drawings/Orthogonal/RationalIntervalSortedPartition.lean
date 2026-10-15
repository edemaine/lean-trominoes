/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalIntervalOrder
import Mathlib.Data.List.Sort

/-! # Sorting a finite interval cover produces its unique consecutive joins -/
namespace LeanTrominoes.RationalIntervalPartition

def sortIntervals (pieces : List Interval) : List Interval :=
  pieces.mergeSort (fun first last => decide (first.start ≤ last.start))

theorem sortIntervals_perm (pieces : List Interval) : (sortIntervals pieces).Perm pieces :=
  List.mergeSort_perm ..

theorem sortIntervals_ordered (pieces : List Interval) :
    (sortIntervals pieces).Pairwise (fun first last => first.start ≤ last.start) := by
  have order := List.pairwise_mergeSort (le := fun first last : Interval => decide (first.start ≤ last.start))
    (by intro first middle last fm ml; simp only [decide_eq_true_eq] at *; exact le_trans fm ml)
    (by intro first last; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _) pieces
  simpa only [sortIntervals,decide_eq_true_eq] using order

theorem pairwise_disjoint_of_nodup (pieces : List Interval) (nodup : pieces.Nodup)
    (disjoint : ∀ first ∈ pieces, ∀ last ∈ pieces, first ≠ last → first.InteriorsDisjoint last) :
    pieces.Pairwise Interval.InteriorsDisjoint := by
  induction pieces with
  | nil => simp
  | cons first rest ih =>
    have data := List.nodup_cons.mp nodup
    apply List.pairwise_cons.mpr
    refine ⟨?_,?_⟩
    · intro last member
      apply disjoint first (by simp) last (List.mem_cons_of_mem first member)
      intro equal
      exact data.1 (by simpa only [equal] using member)
    · exact ih data.2 (fun a am b bm different => disjoint a (List.mem_cons_of_mem first am) b (List.mem_cons_of_mem first bm) different)

theorem sortIntervals_cover_chain (pieces : List Interval) (nodup : pieces.Nodup) (left right : ℚ)
    (positive : left < right)
    (disjoint : ∀ first ∈ pieces, ∀ last ∈ pieces, first ≠ last → first.InteriorsDisjoint last)
    (bounds : ∀ piece ∈ pieces, left ≤ piece.start ∧ piece.finish ≤ right)
    (cover : ∀ point, left < point → point < right → ∃ piece ∈ pieces, piece.Contains point) :
    (sortIntervals pieces).head?.map Interval.start = some left ∧
      (sortIntervals pieces).getLast?.map Interval.finish = some right ∧
      (sortIntervals pieces).IsChain (fun first last => first.finish = last.start) := by
  have perm := sortIntervals_perm pieces
  have sortedCover : ∀ point, left < point → point < right → ∃ piece ∈ sortIntervals pieces, piece.Contains point := by
    intro point after before
    obtain ⟨piece,member,contains⟩ := cover point after before
    exact ⟨piece,perm.mem_iff.mpr member,contains⟩
  have nonempty : sortIntervals pieces ≠ [] := by
    intro empty
    obtain ⟨piece,member,_⟩ := sortedCover ((left+right)/2) (by linarith) (by linarith)
    simp [empty] at member
  apply disjoint_ordered_cover_chain _ nonempty left right positive (sortIntervals_ordered pieces)
    (pairwise_disjoint_of_nodup _ (perm.nodup_iff.mpr nodup)
      (fun a am b bm different => disjoint a (perm.mem_iff.mp am) b (perm.mem_iff.mp bm) different))
    (fun piece member => bounds piece (perm.mem_iff.mp member)) sortedCover

end LeanTrominoes.RationalIntervalPartition
