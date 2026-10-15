/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleNewCutPortClassification
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleVerticalPortPositions
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceEndpointData

/-! # New cut-boundary positions recover the original edge parameter exactly -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem rectanglePort_new_cut_recovers_parameter {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) (line : Int) (right : Bool) (parameter : ℚ)
    {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (oldPoint : (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter =
      rectanglePortOriginalPoint graph drawing column cell key)
    (onCut : (rectangleLiftedPortPoint graph drawing column cell key).1 =
      (paddedRefinementFactor drawing.gridSize : Int)*line+(if right then -5 else 5)*crossingBound drawing.gridSize)
    (nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1) :
    parameter = (drawing.liftedStraightSegment index (0,0)).rationalXParameter
      ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) := by
  obtain ⟨lineEq,raw,keyEq⟩ := rectanglePort_at_new_cut_boundary planar degree graphLocal straight column cell line right valid onCut
  have castLine : (line : ℚ) = (column : ℚ)+(if right then 1 else 0)+(drawing.gridSize : ℚ)*cell.1 := by
    cases right <;> exact_mod_cast lineEq
  have oldX := congrArg Prod.fst oldPoint
  rw [keyEq,rectangle_vertical_original_point_x] at oldX
  have pointX : ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter parameter).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
    rw [castLine]
    exact oldX
  have parameterEq := congrArg (drawing.liftedStraightSegment index (0,0)).rationalXParameter pointX
  exact (GridSegment.rationalXParameter_xAtParameter nonvertical parameter).symm.trans parameterEq

end LeanTrominoes.PeriodicGridDrawing
