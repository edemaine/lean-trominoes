/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Tactic

/-! # Noncrossing orthogonal routing across an ordered vertical slab

Theorem 2.2 assigns downward tracks from the left boundary and upward tracks
from the right boundary. This module checks all closed segment contacts,
including bends and endpoints, rather than only proper interior crossings.
-/
namespace LeanTrominoes.OrthogonalSlabRouting

def bend (left right gap rank source target : Int) : Int :=
  if target ≤ source then left+gap*rank else right-gap*rank

def segments (left right track source target : Int) : List GridSegment :=
  [⟨(left,source),(track,source)⟩,
   ⟨(track,source),(track,target)⟩,
   ⟨(track,target),(right,target)⟩]

theorem bend_inside {left right gap count rank source target : Int}
    (gapPositive : 0 < gap) (rankPositive : 0 < rank) (rankBound : rank ≤ count)
    (room : left+gap*count < right-gap*count) :
    left < bend left right gap rank source target ∧
      bend left right gap rank source target < right := by
  have rankScale : 0 < gap*rank := mul_pos gapPositive rankPositive
  have scaleBound : gap*rank ≤ gap*count := mul_le_mul_of_nonneg_left rankBound gapPositive.le
  unfold bend
  split <;> constructor <;> omega

private theorem disjoint_segments {left right firstTrack secondTrack firstSource firstTarget secondSource secondTarget : Int}
    (firstInside : left < firstTrack ∧ firstTrack < right)
    (secondInside : left < secondTrack ∧ secondTrack < right)
    (sourceOrder : firstSource < secondSource) (targetOrder : firstTarget < secondTarget)
    (trackOrder :
      (firstTarget ≤ firstSource ∧ secondTarget ≤ secondSource → firstTrack < secondTrack) ∧
      (firstSource < firstTarget ∧ secondSource < secondTarget → secondTrack < firstTrack) ∧
      (firstTarget ≤ firstSource ∧ secondSource < secondTarget → firstTrack < secondTrack) ∧
      (firstSource < firstTarget ∧ secondTarget ≤ secondSource → secondTrack < firstTrack)) :
    ∀ first ∈ segments left right firstTrack firstSource firstTarget,
      ∀ second ∈ segments left right secondTrack secondSource secondTarget,
        ∀ point, ¬ (first.Contains point ∧ second.Contains point) := by
  intro first firstMember second secondMember point both
  simp only [segments,List.mem_cons,List.not_mem_nil,or_false] at firstMember secondMember
  have down : firstTarget ≤ firstSource → firstTrack < secondTrack := by
    intro firstDown
    by_cases secondDown : secondTarget ≤ secondSource
    · exact trackOrder.1 ⟨firstDown,secondDown⟩
    · exact trackOrder.2.2.1 ⟨firstDown,by omega⟩
  have up : firstSource < firstTarget → secondTrack < firstTrack := by
    intro firstUp
    by_cases secondDown : secondTarget ≤ secondSource
    · exact trackOrder.2.2.2 ⟨firstUp,secondDown⟩
    · exact trackOrder.2.1 ⟨firstUp,by omega⟩
  have comparison : if firstTarget ≤ firstSource then firstTrack < secondTrack else secondTrack < firstTrack := by
    split
    · exact down (by assumption)
    · exact up (by omega)
  by_cases firstDown : firstTarget ≤ firstSource
  all_goals simp only [firstDown,ite_true,ite_false] at comparison
  all_goals rcases firstMember with rfl | rfl | rfl
  all_goals rcases secondMember with rfl | rfl | rfl
  all_goals
    simp only [GridSegment.Contains,GridSegment.IsHorizontal,GridSegment.IsVertical,
      GridSegment.Between] at both
    rcases both with ⟨(⟨_,_,(_|_)⟩|⟨_,_,(_|_)⟩),(⟨_,_,(_|_)⟩|⟨_,_,(_|_)⟩)⟩ <;> omega

theorem tracks_disjoint {left right gap count firstRank secondRank firstSource firstTarget secondSource secondTarget : Int}
    (gapPositive : 0 < gap) (firstRankPositive : 0 < firstRank) (rankOrder : firstRank < secondRank)
    (rankBound : secondRank ≤ count) (room : left+gap*count < right-gap*count)
    (sourceOrder : firstSource < secondSource) (targetOrder : firstTarget < secondTarget) :
    ∀ first ∈ segments left right (bend left right gap firstRank firstSource firstTarget) firstSource firstTarget,
      ∀ second ∈ segments left right (bend left right gap secondRank secondSource secondTarget) secondSource secondTarget,
        ∀ point, ¬ (first.Contains point ∧ second.Contains point) := by
  apply disjoint_segments
    (bend_inside gapPositive firstRankPositive (by omega) room)
    (bend_inside gapPositive (by omega) rankBound room) sourceOrder targetOrder
  have scaledOrder : gap*firstRank < gap*secondRank := mul_lt_mul_of_pos_left rankOrder gapPositive
  have firstBound : gap*firstRank ≤ gap*count := mul_le_mul_of_nonneg_left (by omega) gapPositive.le
  have secondBound : gap*secondRank ≤ gap*count := mul_le_mul_of_nonneg_left rankBound gapPositive.le
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro directions
  · simp only [bend,if_pos directions.1,if_pos directions.2]
    omega
  · simp only [bend,if_neg (by omega : ¬ firstTarget ≤ firstSource),if_neg (by omega : ¬ secondTarget ≤ secondSource)]
    omega
  · simp only [bend,if_pos directions.1,if_neg (by omega : ¬ secondTarget ≤ secondSource)]
    omega
  · simp only [bend,if_neg (by omega : ¬ firstTarget ≤ firstSource),if_pos directions.2]
    omega

end LeanTrominoes.OrthogonalSlabRouting
