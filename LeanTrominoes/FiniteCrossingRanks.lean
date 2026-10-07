/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalDrawingRefinementBounds
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-! # Computable increasing ranks for finite rational crossing heights -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def crossingRank (heights : Finset ℚ) (height : ℚ) : Nat :=
  1+(heights.filter (fun other => other < height)).card

theorem crossingRank_positive (heights : Finset ℚ) (height : ℚ) : 0 < crossingRank heights height := by
  unfold crossingRank
  omega

theorem crossingRank_le_card {heights : Finset ℚ} {height : ℚ} (member : height ∈ heights) :
    crossingRank heights height ≤ heights.card := by
  have proper : heights.filter (fun other => other < height) ⊂ heights := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro equal
    have inFilter : height ∈ heights.filter (fun other => other < height) := by rw [equal]; exact member
    exact (lt_irrefl height) (Finset.mem_filter.mp inFilter).2
  have count := Finset.card_lt_card proper
  unfold crossingRank
  omega

theorem crossingRank_strictMonoOn (heights : Finset ℚ) : StrictMonoOn (crossingRank heights) heights := by
  intro first fm second _ ordered
  have proper : heights.filter (fun other => other < first) ⊂ heights.filter (fun other => other < second) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro height member
      have data := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr ⟨data.1,data.2.trans ordered⟩
    · intro equal
      have inSecond : first ∈ heights.filter (fun other => other < second) := Finset.mem_filter.mpr ⟨fm,ordered⟩
      rw [← equal] at inSecond
      exact (lt_irrefl first) (Finset.mem_filter.mp inSecond).2
  have count := Finset.card_lt_card proper
  unfold crossingRank
  omega

theorem ranked_crossingCoordinate_strictMonoOn (heights : Finset ℚ) (count lower upper : Int)
    (ordered : lower < upper) :
    StrictMonoOn (fun height => crossingCoordinate count lower upper (crossingRank heights height)) heights := by
  intro first fm second sm comparison
  apply crossingCoordinate_strictMono ordered
  exact_mod_cast crossingRank_strictMonoOn heights fm sm comparison

theorem ranked_crossingCoordinate_outside_rectangles {heights : Finset ℚ} {height : ℚ} (member : height ∈ heights)
    {count lower upper : Int} (ordered : lower < upper) (countBound : (heights.card : Int) ≤ count) :
    vertexCoordinate count lower+10 < crossingCoordinate count lower upper (crossingRank heights height) ∧
      crossingCoordinate count lower upper (crossingRank heights height) < vertexCoordinate count upper-10 := by
  apply crossingCoordinate_outside_rectangles ordered
  · exact_mod_cast crossingRank_positive heights height
  · have rankBound : (crossingRank heights height : Int) ≤ heights.card := by
      exact_mod_cast crossingRank_le_card member
    exact rankBound.trans countBound

end LeanTrominoes.OrthogonalDrawingRefinement
