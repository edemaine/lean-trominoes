/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.FiniteHeightBrackets
import LeanTrominoes.SAT.Planar.FiniteCrossingRanks

/-! # Crossing redistribution preserves order across all vertex-height brackets -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def heightsInBracket (levels : Finset Int) (heights : Finset ℚ) (height : ℚ) : Finset ℚ :=
  heights.filter (fun other => (lowerHeight levels height : ℚ) ≤ other ∧ other < (upperHeight levels height : ℚ))

def redistributedHeight (levels : Finset Int) (heights : Finset ℚ) (count : Int) (height : ℚ) : Int :=
  crossingCoordinate count (lowerHeight levels height) (upperHeight levels height)
    (crossingRank (heightsInBracket levels heights height) height)

theorem self_mem_heightsInBracket {levels : Finset Int} {heights : Finset ℚ} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) : height ∈ heightsInBracket levels heights height :=
  Finset.mem_filter.mpr ⟨member,(lowerHeight_spec lowerPresent).2.1,(upperHeight_spec upperPresent).2.1⟩

theorem vertexCoordinate_monotone {count : Int} (nonnegative : 0 ≤ count) : Monotone (vertexCoordinate count) := by
  intro first second ordered
  unfold vertexCoordinate
  nlinarith

theorem redistributedHeight_bounds {levels : Finset Int} {heights : Finset ℚ} {count : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count) :
    vertexCoordinate count (lowerHeight levels height)+10 < redistributedHeight levels heights count height ∧
      redistributedHeight levels heights count height < vertexCoordinate count (upperHeight levels height)-10 := by
  apply ranked_crossingCoordinate_outside_rectangles
    (self_mem_heightsInBracket member lowerPresent upperPresent) (height_bracket_ordered lowerPresent upperPresent)
  have filtered : (heightsInBracket levels heights height).card ≤ heights.card := Finset.card_filter_le _ _
  have castBound : ((heightsInBracket levels heights height).card : Int) ≤ heights.card := by exact_mod_cast filtered
  exact castBound.trans countBound

theorem redistributedHeight_strictMonoOn (levels : Finset Int) (heights : Finset ℚ) {count : Int}
    (present : ∀ height ∈ heights, (lowerLevels levels height).Nonempty ∧ (upperLevels levels height).Nonempty)
    (countBound : (heights.card : Int) ≤ count) : StrictMonoOn (redistributedHeight levels heights count) heights := by
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
    unfold redistributedHeight
    rw [← same.1,← same.2,← sameHeights]
    apply crossingCoordinate_strictMono (height_bracket_ordered firstPresent.1 firstPresent.2)
    exact_mod_cast ranks
  · have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
    have between := vertexCoordinate_monotone nonnegative separated
    have firstBounds := redistributedHeight_bounds firstMember firstPresent.1 firstPresent.2 countBound
    have secondBounds := redistributedHeight_bounds secondMember secondPresent.1 secondPresent.2 countBound
    omega

theorem redistributedHeight_below_vertex {levels : Finset Int} {heights : Finset ℚ} {count level : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count)
    (levelMember : level ∈ levels) (below : height < (level : ℚ)) :
    redistributedHeight levels heights count height < vertexCoordinate count level-10 := by
  have upperBound := (upperHeight_spec upperPresent).2.2 level levelMember below
  have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
  have bound := vertexCoordinate_monotone nonnegative upperBound
  have gap := (redistributedHeight_bounds member lowerPresent upperPresent countBound).2
  omega

theorem redistributedHeight_above_vertex {levels : Finset Int} {heights : Finset ℚ} {count level : Int} {height : ℚ}
    (member : height ∈ heights) (lowerPresent : (lowerLevels levels height).Nonempty)
    (upperPresent : (upperLevels levels height).Nonempty) (countBound : (heights.card : Int) ≤ count)
    (levelMember : level ∈ levels) (above : (level : ℚ) ≤ height) :
    vertexCoordinate count level+10 < redistributedHeight levels heights count height := by
  have lowerBound := (lowerHeight_spec lowerPresent).2.2 level levelMember above
  have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
  have bound := vertexCoordinate_monotone nonnegative lowerBound
  have gap := (redistributedHeight_bounds member lowerPresent upperPresent countBound).1
  omega

end LeanTrominoes.OrthogonalDrawingRefinement
