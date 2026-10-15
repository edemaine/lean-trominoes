/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRouteWord
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalIntervalSortedPartition

/-! # Assemble replacement routes in the order of their original edge intervals -/
namespace LeanTrominoes.GridPolyline
open RationalIntervalPartition PeriodicOrthocrossing

def assembleIntervals (pieces : List Interval) (route : Interval → List Cell) : List Cell :=
  joinWord ((sortIntervals pieces).map route)

theorem assembleIntervals_valid (pieces : List Interval) (nodup : pieces.Nodup) (route : Interval → List Cell)
    (left right : ℚ) (positive : left < right)
    (disjoint : ∀ first ∈ pieces, ∀ last ∈ pieces, first ≠ last → first.InteriorsDisjoint last)
    (bounds : ∀ piece ∈ pieces, left ≤ piece.start ∧ piece.finish ≤ right)
    (cover : ∀ point, left < point → point < right → ∃ piece ∈ pieces, piece.Contains point)
    (simple : ∀ piece ∈ pieces, IsRealOpenSimple (route piece))
    (orthogonal : ∀ piece ∈ pieces, OrthogonalPolyline (route piece))
    (joins : ∀ first ∈ pieces, ∀ last ∈ pieces, first.finish = last.start → (route first).getLast? = (route last).head?)
    (separated : SeparatedWord ((sortIntervals pieces).map route)) (source target : Cell)
    (sourceMatch : ∀ piece ∈ pieces, piece.start = left → (route piece).head? = some source)
    (targetMatch : ∀ piece ∈ pieces, piece.finish = right → (route piece).getLast? = some target) :
    IsRealOpenSimple (assembleIntervals pieces route) ∧ OrthogonalPolyline (assembleIntervals pieces route) ∧
      (assembleIntervals pieces route).head? = some source ∧ (assembleIntervals pieces route).getLast? = some target ∧
      ∀ point, RealContains (assembleIntervals pieces route) point ↔ ∃ piece ∈ pieces, RealContains (route piece) point := by
  have partition := sortIntervals_cover_chain pieces nodup left right positive disjoint bounds cover
  have perm := sortIntervals_perm pieces
  have chain : ((sortIntervals pieces).map route).IsChain (fun first last => first.getLast? = last.head?) := by
    apply (List.isChain_map route).mpr
    exact partition.2.2.imp_of_mem_imp (fun first last fm lm equal => joins first (perm.mem_iff.mp fm) last (perm.mem_iff.mp lm) equal)
  have sortedSimple : ∀ part ∈ (sortIntervals pieces).map route, IsRealOpenSimple part := by
    intro part member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    exact simple piece (perm.mem_iff.mp pieceMember)
  have sortedOrthogonal : ∀ part ∈ (sortIntervals pieces).map route, OrthogonalPolyline part := by
    intro part member
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
    exact orthogonal piece (perm.mem_iff.mp pieceMember)
  cases sorted : sortIntervals pieces with
  | nil => simp [sorted] at partition
  | cons first rest =>
    rw [sorted] at partition perm chain sortedSimple sortedOrthogonal separated
    have firstMember : first ∈ pieces := perm.mem_iff.mp (by simp)
    have firstStart : first.start = left := by simpa using partition.1
    have word := joinWord_valid sortedSimple sortedOrthogonal chain separated
    unfold assembleIntervals
    rw [sorted]
    refine ⟨word.1,word.2.1,word.2.2.1.trans (sourceMatch first firstMember firstStart),?_,?_⟩
    · have lastPresent : (first :: rest).getLast? ≠ none := by simp
      cases last : (first :: rest).getLast? with
      | none => exact (lastPresent last).elim
      | some piece =>
        have pieceMember : piece ∈ pieces := perm.mem_iff.mp (List.mem_of_mem_getLast? (by simp [last]))
        have finish : piece.finish = right := by simpa [last] using partition.2.1
        change (joinWord (route first :: rest.map route)).getLast? = _
        rw [word.2.2.2.1]
        change ((first :: rest).map route).getLast?.bind List.getLast? = _
        simp only [List.getLast?_map,last,Option.map_some,Option.bind_some]
        exact targetMatch piece pieceMember finish
    · intro point
      change RealContains (joinWord (route first :: rest.map route)) point ↔ _
      rw [word.2.2.2.2]
      constructor
      · rintro ⟨part,member,contains⟩
        change part ∈ (first :: rest).map route at member
        obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp member
        exact ⟨piece,perm.mem_iff.mp pieceMember,contains⟩
      · rintro ⟨piece,member,contains⟩
        exact ⟨route piece,List.mem_map.mpr ⟨piece,perm.mem_iff.mpr member,rfl⟩,contains⟩

end LeanTrominoes.GridPolyline
