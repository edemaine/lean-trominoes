/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedPeriodicColumnRefinement
import LeanTrominoes.PeriodicHeightClearance

/-! # Padded column crossings clear every translated vertex rectangle -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem paddedCrossingHeight_avoids_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ} {point : Cell}
    (member : height ∈ verticalCrossingHeights graph drawing line)
    (pointMember : point ∈ drawing.vertexPositions) (sameX : point.1 = line) :
    30*(crossingBound drawing.gridSize : Int)+10 <
      |paddedCrossingHeight graph drawing line height-(paddedRefinementFactor drawing.gridSize : Int)*point.2| := by
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  rcases lt_or_ge height (point.2 : ℚ) with below | above
  · have gap := paddedCrossingHeight_below_vertex compatible degree member pointMember sameX below
    have difference : paddedCrossingHeight graph drawing line height-(paddedRefinementFactor drawing.gridSize : Int)*point.2 <
        -(30*crossingBound drawing.gridSize+10) := by omega
    rw [abs_of_neg (by omega)]
    omega
  · have gap := paddedCrossingHeight_above_vertex compatible degree member pointMember sameX above
    have difference : 30*(crossingBound drawing.gridSize : Int)+10 <
        paddedCrossingHeight graph drawing line height-(paddedRefinementFactor drawing.gridSize : Int)*point.2 := by omega
    rw [abs_of_pos (by omega)]
    exact difference

theorem paddedPeriodicColumnHeight_avoids_lifted_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : rationalResidue drawing.gridSize height ∈ verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    {position : Cell} (positionMember : position ∈ drawing.vertexPositions) (vertexCell : Cell)
    (sameX : (Cell.add position (drawing.periodTranslation vertexCell)).1 = line) :
    30*(crossingBound drawing.gridSize : Int)+10 < |paddedPeriodicColumnHeight graph drawing line height-
      (paddedRefinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation vertexCell)).2| := by
  have inside := compatible.2.2.2.2.1 position positionMember
  have lineMod : line % (drawing.gridSize : Int) = position.1 := by
    rw [← sameX]
    simp only [Cell.add,periodTranslation,Cell.scale,Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt inside.1.le inside.2.1
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by
    exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have marginNonnegative : (0 : Int) ≤ 30*crossingBound drawing.gridSize+10 := by positivity
  have finiteBounds := paddedCrossingHeight_in_cell compatible degree member
  have finiteGap := paddedCrossingHeight_avoids_vertex compatible degree member positionMember lineMod.symm
  unfold paddedPeriodicColumnHeight
  simp only [paddedGridSize,Nat.cast_mul,Cell.add,periodTranslation,Cell.scale]
  apply periodicRedistributedHeight_vertex_clearance factorPositive marginNonnegative
    ⟨inside.2.2.1,inside.2.2.2⟩ _ height
  · simpa only [paddedGridSize,Nat.cast_mul] using finiteBounds
  · exact finiteGap

end LeanTrominoes.PeriodicGridDrawing
