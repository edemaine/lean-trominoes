/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedVertexClearance
import LeanTrominoes.OrthogonalEnlargedCrossingBars

/-! # Padded wide crossing bars avoid all periodic enlarged vertex connectors -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem paddedCrossingBar_avoids_lifted_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : rationalResidue drawing.gridSize height ∈ verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    {position : Cell} (positionMember : position ∈ drawing.vertexPositions) (vertexCell : Cell)
    (profile : AnchorProfile) (index : Fin 4) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains
      (enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line
        (paddedPeriodicColumnHeight graph drawing line height)) point)
    (templateContains : GridPolyline.RealContains
      (enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
        (Cell.add position (drawing.periodTranslation vertexCell)) profile index) point) : False := by
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  apply enlargedCrossingBar_avoids_rectangle spacing profile index _ barContains templateContains
  intro sameX
  have gap := paddedPeriodicColumnHeight_avoids_lifted_vertex compatible degree member positionMember vertexCell sameX
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  omega

end LeanTrominoes.PeriodicGridDrawing
