/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.FiniteHeightRedistribution
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalDrawingPaddedRefinementBounds

/-! # Order-preserving redistribution with margins linear in the crossing count -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def paddedRedistributedHeight (levels : Finset Int) (heights : Finset ℚ) (count : Int) (height : ℚ) : Int :=
  paddedCrossingCoordinate count (lowerHeight levels height) (upperHeight levels height)
    (crossingRank (heightsInBracket levels heights height) height)

theorem paddedRedistributedHeight_bounds {levels : Finset Int} {heights : Finset ℚ} {count : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count) :
    vertexCoordinate (3*count) (lowerHeight levels height)+(30*count+10) < paddedRedistributedHeight levels heights count height ∧
      paddedRedistributedHeight levels heights count height < vertexCoordinate (3*count) (upperHeight levels height)-(30*count+10) := by
  have filtered : (heightsInBracket levels heights height).card ≤ heights.card := Finset.card_filter_le _ _
  have castBound : ((heightsInBracket levels heights height).card : Int) ≤ heights.card := by exact_mod_cast filtered
  have rankCardBound : (crossingRank (heightsInBracket levels heights height) height : Int) ≤
      (heightsInBracket levels heights height).card := by
    exact_mod_cast crossingRank_le_card (self_mem_heightsInBracket member lowerPresent upperPresent)
  have rankBound : (crossingRank (heightsInBracket levels heights height) height : Int) ≤ count :=
    rankCardBound.trans (castBound.trans countBound)
  exact paddedCrossingCoordinate_clearance
    (le_trans (by positivity : (0 : Int) ≤ heights.card) countBound)
    (height_bracket_ordered lowerPresent upperPresent)
    (by exact_mod_cast crossingRank_positive (heightsInBracket levels heights height) height) rankBound

theorem paddedRedistributedHeight_strictMonoOn (levels : Finset Int) (heights : Finset ℚ) {count : Int}
    (present : ∀ height ∈ heights, (lowerLevels levels height).Nonempty ∧ (upperLevels levels height).Nonempty)
    (countBound : (heights.card : Int) ≤ count) : StrictMonoOn (paddedRedistributedHeight levels heights count) heights := by
  intro first firstMember second secondMember ordered
  have firstPresent := present first firstMember
  have secondPresent := present second secondMember
  have brackets := height_brackets_same_or_separated ordered.le firstPresent.1 firstPresent.2 secondPresent.1 secondPresent.2
  rcases brackets with same | separated
  · have sameHeights : heightsInBracket levels heights first = heightsInBracket levels heights second := by
      simp only [heightsInBracket,same.1,same.2]
    have firstIn := self_mem_heightsInBracket firstMember firstPresent.1 firstPresent.2
    have secondIn := self_mem_heightsInBracket secondMember secondPresent.1 secondPresent.2
    rw [← sameHeights] at secondIn
    have ranks := crossingRank_strictMonoOn (heightsInBracket levels heights first) firstIn secondIn ordered
    unfold paddedRedistributedHeight
    rw [← same.1,← same.2,← sameHeights]
    apply paddedCrossingCoordinate_strictMono (height_bracket_ordered firstPresent.1 firstPresent.2)
    exact_mod_cast ranks
  · have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
    have between := vertexCoordinate_monotone (by omega : 0 ≤ 3*count) separated
    have firstBounds := paddedRedistributedHeight_bounds firstMember firstPresent.1 firstPresent.2 countBound
    have secondBounds := paddedRedistributedHeight_bounds secondMember secondPresent.1 secondPresent.2 countBound
    omega

theorem paddedRedistributedHeight_below_vertex {levels : Finset Int} {heights : Finset ℚ} {count level : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count)
    (levelMember : level ∈ levels) (below : height < (level : ℚ)) :
    paddedRedistributedHeight levels heights count height < vertexCoordinate (3*count) level-(30*count+10) := by
  have upperBound := (upperHeight_spec upperPresent).2.2 level levelMember below
  have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
  have bound := vertexCoordinate_monotone (by omega : 0 ≤ 3*count) upperBound
  have gap := (paddedRedistributedHeight_bounds member lowerPresent upperPresent countBound).2
  omega

theorem paddedRedistributedHeight_above_vertex {levels : Finset Int} {heights : Finset ℚ} {count level : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count)
    (levelMember : level ∈ levels) (above : (level : ℚ) ≤ height) :
    vertexCoordinate (3*count) level+(30*count+10) < paddedRedistributedHeight levels heights count height := by
  have lowerBound := (lowerHeight_spec lowerPresent).2.2 level levelMember above
  have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
  have bound := vertexCoordinate_monotone (by omega : 0 ≤ 3*count) lowerBound
  have gap := (paddedRedistributedHeight_bounds member lowerPresent upperPresent countBound).1
  omega

end LeanTrominoes.OrthogonalDrawingRefinement
