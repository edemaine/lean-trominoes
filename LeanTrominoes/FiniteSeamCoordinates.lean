/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalSlabAssignment
import LeanTrominoes.FiniteHeightPaddedRedistribution

/-! # Order-preserving integral ports on periodic row seams -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def seamCrossingsInSlab (heights : Finset ℚ) (bias : ℚ → Bool) (coordinate : ℚ) : Finset ℚ :=
  heights.filter fun other => rationalSlab other (bias other) = rationalSlab coordinate (bias coordinate)

def seamCoordinate (heights : Finset ℚ) (bias : ℚ → Bool) (count : Int) (coordinate : ℚ) : Int :=
  vertexCoordinate (3*count) (rationalSlab coordinate (bias coordinate))+15*count+
    20*crossingRank (seamCrossingsInSlab heights bias coordinate) coordinate

theorem self_mem_seamCrossingsInSlab {heights : Finset ℚ} (bias : ℚ → Bool) {coordinate : ℚ}
    (member : coordinate ∈ heights) : coordinate ∈ seamCrossingsInSlab heights bias coordinate :=
  Finset.mem_filter.mpr ⟨member,rfl⟩

theorem seamCoordinate_bounds {heights : Finset ℚ} (bias : ℚ → Bool) {count : Int} {coordinate : ℚ}
    (member : coordinate ∈ heights) (countBound : (heights.card : Int) ≤ count) :
    vertexCoordinate (3*count) (rationalSlab coordinate (bias coordinate))+5*count+2*count <
      seamCoordinate heights bias count coordinate ∧
    seamCoordinate heights bias count coordinate <
      vertexCoordinate (3*count) (rationalSlab coordinate (bias coordinate)+1)-5*count-2*count := by
  have rankPositive : (0 : Int) < crossingRank (seamCrossingsInSlab heights bias coordinate) coordinate := by
    exact_mod_cast crossingRank_positive (seamCrossingsInSlab heights bias coordinate) coordinate
  have rankCard : (crossingRank (seamCrossingsInSlab heights bias coordinate) coordinate : Int) ≤
      (seamCrossingsInSlab heights bias coordinate).card := by
    exact_mod_cast crossingRank_le_card (self_mem_seamCrossingsInSlab bias member)
  have filtered : ((seamCrossingsInSlab heights bias coordinate).card : Int) ≤ heights.card := by
    exact_mod_cast Finset.card_filter_le heights (fun other => rationalSlab other (bias other) = rationalSlab coordinate (bias coordinate))
  have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
  unfold seamCoordinate vertexCoordinate
  constructor <;> nlinarith

theorem seamCoordinate_strictMonoOn (heights : Finset ℚ) (bias : ℚ → Bool) {count : Int}
    (countBound : (heights.card : Int) ≤ count) : StrictMonoOn (seamCoordinate heights bias count) heights := by
  intro first firstMember second secondMember ordered
  have slabs := rationalSlab_order ordered (bias first) (bias second)
  rcases lt_or_eq_of_le slabs with separated | same
  · have firstBounds := seamCoordinate_bounds bias firstMember countBound
    have secondBounds := seamCoordinate_bounds bias secondMember countBound
    have nonnegative : (0 : Int) ≤ count := le_trans (by positivity : (0 : Int) ≤ heights.card) countBound
    have between := vertexCoordinate_monotone (by omega : 0 ≤ 3*count)
      (by omega : rationalSlab first (bias first)+1 ≤ rationalSlab second (bias second))
    omega
  · have sameCrossings : seamCrossingsInSlab heights bias first = seamCrossingsInSlab heights bias second := by
      simp only [seamCrossingsInSlab,same]
    have firstIn := self_mem_seamCrossingsInSlab bias firstMember
    have secondIn := self_mem_seamCrossingsInSlab bias secondMember
    rw [← sameCrossings] at secondIn
    have ranks : (crossingRank (seamCrossingsInSlab heights bias first) first : Int) <
        crossingRank (seamCrossingsInSlab heights bias first) second := by
      exact_mod_cast crossingRank_strictMonoOn _ firstIn secondIn ordered
    unfold seamCoordinate
    rw [same,sameCrossings]
    rw [sameCrossings] at ranks
    omega

end LeanTrominoes.OrthogonalDrawingRefinement
