/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalSlabRealRouting

/-! # Integral spacing and the cubic grid bound in Theorem 2.2

The factor sixty clears both the crossing ranks and the half-integral
rectangle anchors. The crossing bound is chosen quadratically even when
the input drawing has fewer edges, so the vertex rectangles also stay
small relative to nonincident input segments.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def crossingBound (grid : Nat) : Nat := 18*grid^2
def gridSize (grid : Nat) : Nat := 60*grid*(crossingBound grid+1)
def vertexCoordinate (count coordinate : Int) : Int := 60*(count+1)*coordinate
def crossingCoordinate (count lower upper rank : Int) : Int :=
  60*((count+1)*lower+rank*(upper-lower))

theorem gridSize_positive {grid : Nat} (positive : 0 < grid) : 0 < gridSize grid := by
  unfold gridSize
  positivity

theorem gridSize_cubic {grid : Nat} (positive : 0 < grid) : gridSize grid ≤ 1140*grid^3 := by
  unfold gridSize crossingBound
  have squarePositive : 1 ≤ grid^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left (60*grid) squarePositive]

theorem crossingCoordinate_strictMono {count lower upper : Int} (ordered : lower < upper) :
    StrictMono (crossingCoordinate count lower upper) := by
  intro first second ranks
  have product : first*(upper-lower) < second*(upper-lower) :=
    mul_lt_mul_of_pos_right ranks (by omega)
  unfold crossingCoordinate
  omega

theorem crossingCoordinate_outside_rectangles {count lower upper rank : Int}
    (ordered : lower < upper) (rankPositive : 0 < rank) (rankBound : rank ≤ count) :
    vertexCoordinate count lower+10 < crossingCoordinate count lower upper rank ∧
      crossingCoordinate count lower upper rank < vertexCoordinate count upper-10 := by
  have firstGap : 1 ≤ rank*(upper-lower) := by nlinarith
  have secondGap : 1 ≤ (count+1-rank)*(upper-lower) := by nlinarith
  unfold vertexCoordinate crossingCoordinate
  constructor <;> nlinarith

theorem slab_room {count left right : Int} (countNonnegative : 0 ≤ count)
    (ordered : left < right) :
    (vertexCoordinate count left+5)+20*count <
      (vertexCoordinate count right-5)-20*count := by
  have separation : count+1 ≤ (count+1)*(right-left) := by nlinarith
  unfold vertexCoordinate
  nlinarith

theorem slab_tracks_disjoint {count left right firstRank secondRank firstSource firstTarget secondSource secondTarget : Int}
    (countNonnegative : 0 ≤ count) (ordered : left < right)
    (firstRankPositive : 0 < firstRank) (rankOrder : firstRank < secondRank)
    (rankBound : secondRank ≤ count)
    (sourceOrder : firstSource < secondSource) (targetOrder : firstTarget < secondTarget) :
    let l := vertexCoordinate count left+5
    let r := vertexCoordinate count right-5
    ∀ first ∈ OrthogonalSlabRouting.segments l r
        (OrthogonalSlabRouting.bend l r 20 firstRank firstSource firstTarget) firstSource firstTarget,
      ∀ second ∈ OrthogonalSlabRouting.segments l r
          (OrthogonalSlabRouting.bend l r 20 secondRank secondSource secondTarget) secondSource secondTarget,
        ∀ point : ℝ × ℝ, ¬ (first.RealContains point ∧ second.RealContains point) :=
  OrthogonalSlabRouting.real_tracks_disjoint (by norm_num) firstRankPositive rankOrder rankBound
    (slab_room countNonnegative ordered) sourceOrder targetOrder

end LeanTrominoes.OrthogonalDrawingRefinement
