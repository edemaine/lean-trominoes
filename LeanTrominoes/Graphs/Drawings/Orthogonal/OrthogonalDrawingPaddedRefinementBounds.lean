/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.OrthogonalDrawingRefinementBounds

/-! # Cubic refinement with margins for nested row-seam routing -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def paddedCrossingCoordinate (count lower upper rank : Int) : Int :=
  crossingCoordinate (3*count) lower upper (count+rank)

def paddedRefinementFactor (grid : Nat) : Nat := 60*(3*crossingBound grid+1)
def paddedGridSize (grid : Nat) : Nat := paddedRefinementFactor grid*grid

theorem paddedCrossingCoordinate_strictMono {count lower upper : Int} (ordered : lower < upper) :
    StrictMono (paddedCrossingCoordinate count lower upper) := by
  intro first second ranks
  exact crossingCoordinate_strictMono ordered (by omega : count+first < count+second)

theorem paddedCrossingCoordinate_clearance {count lower upper rank : Int}
    (nonnegative : 0 ≤ count) (ordered : lower < upper) (rankPositive : 0 < rank) (rankBound : rank ≤ count) :
    vertexCoordinate (3*count) lower+(30*count+10) < paddedCrossingCoordinate count lower upper rank ∧
      paddedCrossingCoordinate count lower upper rank < vertexCoordinate (3*count) upper-(30*count+10) := by
  have firstGap : count+1 ≤ (count+rank)*(upper-lower) := by nlinarith
  have secondGap : count+1 ≤ (2*count+1-rank)*(upper-lower) := by nlinarith
  unfold vertexCoordinate paddedCrossingCoordinate crossingCoordinate
  constructor <;> nlinarith

theorem paddedRefinementFactor_positive (grid : Nat) : 0 < paddedRefinementFactor grid := by
  unfold paddedRefinementFactor
  omega

theorem paddedGridSize_positive {grid : Nat} (positive : 0 < grid) : 0 < paddedGridSize grid :=
  Nat.mul_pos (paddedRefinementFactor_positive grid) positive

theorem paddedGridSize_cubic {grid : Nat} (positive : 0 < grid) : paddedGridSize grid ≤ 3300*grid^3 := by
  unfold paddedGridSize paddedRefinementFactor crossingBound
  have squarePositive : 1 ≤ grid^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left grid squarePositive]

theorem padded_slab_room (count : Nat) :
    4*(count : Int) < 60*(3*(count : Int)+1)-10*count := by omega

theorem padded_vertexCoordinate_eq_factor (grid : Nat) (coordinate : Int) :
    vertexCoordinate (3*(crossingBound grid : Int)) coordinate = (paddedRefinementFactor grid : Int)*coordinate := by
  simp [vertexCoordinate,paddedRefinementFactor,Nat.cast_add,Nat.cast_mul]

theorem padded_rectangle_inside_cell {grid : Nat} (positive : 0 < grid) {coordinate : Int}
    (lower : 0 < coordinate) (upper : coordinate < grid) :
    0 < (paddedRefinementFactor grid : Int)*coordinate-10*crossingBound grid ∧
      (paddedRefinementFactor grid : Int)*coordinate+10*crossingBound grid < paddedGridSize grid := by
  have factorPositive : (0 : Int) < paddedRefinementFactor grid := by exact_mod_cast paddedRefinementFactor_positive grid
  have factorRoom : 10*(crossingBound grid : Int) < paddedRefinementFactor grid := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound grid := by positivity
    omega
  have first : (paddedRefinementFactor grid : Int) ≤ (paddedRefinementFactor grid : Int)*coordinate := by nlinarith
  have second : (paddedRefinementFactor grid : Int) ≤ (paddedRefinementFactor grid : Int)*((grid : Int)-coordinate) := by nlinarith
  unfold paddedGridSize
  push_cast
  constructor <;> nlinarith

end LeanTrominoes.OrthogonalDrawingRefinement
