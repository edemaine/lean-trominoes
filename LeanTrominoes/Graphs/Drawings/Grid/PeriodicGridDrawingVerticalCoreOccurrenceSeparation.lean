/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentVerticalCoreInterior
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightInteriorsDisjoint
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedIncidenceRoutes

/-! # Shortened vertical cores of distinct periodic edge occurrences are disjoint -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem verticalCore_occurrences_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (firstStraight : (drawing.edgeRoute first.2).length = 2) (lastStraight : (drawing.edgeRoute last.2).length = 2)
    (firstCell lastCell : Cell) (different : (first.2,firstCell) ≠ (last.2,lastCell))
    (firstVertical : (drawing.liftedStraightSegment first.2 firstCell).IsVertical)
    (lastVertical : (drawing.liftedStraightSegment last.2 lastCell).IsVertical)
    {point : ℝ × ℝ}
    (firstContains : ((drawing.liftedStraightSegment first.2 firstCell).verticalCore
      (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point)
    (lastContains : ((drawing.liftedStraightSegment last.2 lastCell).verticalCore
      (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point) : False := by
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  exact straight_lifted_interiors_disjoint planar firstMember lastMember firstStraight lastStraight firstCell lastCell different
    (GridSegment.verticalCore_inverse_image_interior firstVertical (crossingBound_positive drawing) spacing firstContains)
    (GridSegment.verticalCore_inverse_image_interior lastVertical (crossingBound_positive drawing) spacing lastContains)

end LeanTrominoes.PeriodicGridDrawing
