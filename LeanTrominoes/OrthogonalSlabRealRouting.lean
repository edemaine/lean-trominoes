/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalSlabRouting
import LeanTrominoes.GridSegmentRealIntersection

/-! # Ordered slab tracks are disjoint in the real plane -/
namespace LeanTrominoes.OrthogonalSlabRouting

private theorem axis_representative {left right track source target : Int}
    (inside : left < track ∧ track < right) {segment : GridSegment}
    (member : segment ∈ segments left right track source target) {point : ℝ × ℝ}
    (contains : segment.RealContains point) :
    ∃ representative ∈ segments left right track source target,
      representative.IsAxisAligned ∧ representative.RealContains point := by
  simp only [segments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨_,by simp [segments],Or.inl ⟨rfl,by change left ≠ track; omega⟩,contains⟩
  · by_cases different : source ≠ target
    · exact ⟨_,by simp [segments],Or.inr ⟨rfl,different⟩,contains⟩
    · have equal : source = target := by omega
      obtain ⟨t,_,_,hx,hy⟩ := contains
      have pointEqual : point = ((track : ℝ),(source : ℝ)) := by
        apply Prod.ext
        · simpa using hx
        · simpa [equal] using hy
      subst point
      exact ⟨⟨(left,source),(track,source)⟩,by simp [segments],
        Or.inl ⟨rfl,by change left ≠ track; omega⟩,GridSegment.realContains_finish _⟩
  · exact ⟨_,by simp [segments],Or.inl ⟨rfl,by change track ≠ right; omega⟩,contains⟩

/-- Every pair of distinct ordered tracks has disjoint closed geometric images.
The assertion includes their horizontal pieces, bends, and possibly constant
vertical pieces. -/
theorem real_tracks_disjoint {left right gap count firstRank secondRank firstSource firstTarget secondSource secondTarget : Int}
    (gapPositive : 0 < gap) (firstRankPositive : 0 < firstRank) (rankOrder : firstRank < secondRank)
    (rankBound : secondRank ≤ count) (room : left+gap*count < right-gap*count)
    (sourceOrder : firstSource < secondSource) (targetOrder : firstTarget < secondTarget) :
    ∀ first ∈ segments left right (bend left right gap firstRank firstSource firstTarget) firstSource firstTarget,
      ∀ second ∈ segments left right (bend left right gap secondRank secondSource secondTarget) secondSource secondTarget,
        ∀ point : ℝ × ℝ, ¬ (first.RealContains point ∧ second.RealContains point) := by
  intro first firstMember second secondMember point both
  obtain ⟨firstAxis,firstAxisMember,firstAligned,firstContains⟩ :=
    axis_representative (bend_inside gapPositive firstRankPositive (by omega) room) firstMember both.1
  obtain ⟨secondAxis,secondAxisMember,secondAligned,secondContains⟩ :=
    axis_representative (bend_inside gapPositive (by omega) rankBound room) secondMember both.2
  obtain ⟨witness,firstWitness,secondWitness⟩ :=
    GridSegment.real_intersection_has_integer_witness firstAligned secondAligned firstContains secondContains
  exact tracks_disjoint gapPositive firstRankPositive rankOrder rankBound room sourceOrder targetOrder
    firstAxis firstAxisMember secondAxis secondAxisMember witness ⟨firstWitness,secondWitness⟩

end LeanTrominoes.OrthogonalSlabRouting
