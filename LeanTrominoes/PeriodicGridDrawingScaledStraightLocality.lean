/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRefinedLocalBoxes
import LeanTrominoes.GridSegmentLocalCellContact
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.GridSegmentRealIntersection

/-! # Uniformly scaled straight edges stay in their endpoint cells -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem scaled_straight_segment_isRealLocal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {point : ℝ × ℝ}
    (contains : ((drawing.liftedStraightSegment tagged.2 (0,0)).scale (paddedRefinementFactor drawing.gridSize)).RealContains point) :
    (straightRefinementDrawing graph drawing).RealPointInCell (0,0) point ∨
      (straightRefinementDrawing graph drawing).RealPointInCell tagged.1.offset point := by
  have sourceEq := liftedStraightSegment_start compatible member (0,0)
  have targetEq := liftedStraightSegment_finish compatible member (0,0)
  have sourceBounds := compatible.2.2.2.2.1 _
    (compatible.vertexPosition_mem (port_vertex_mem compatible.1 (sourcePort_mem_allPorts graph member)))
  have targetBounds := compatible.2.2.2.2.1 _
    (compatible.vertexPosition_mem (port_vertex_mem compatible.1 (targetPort_mem_allPorts graph member)))
  change (0 < (drawing.vertexPosition graph tagged.1.source).1 ∧ _ ∧ _ ∧ _) at sourceBounds
  change (0 < (drawing.vertexPosition graph tagged.1.target).1 ∧ _ ∧ _ ∧ _) at targetBounds
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have factorNonnegative : (0 : Int) ≤ paddedRefinementFactor drawing.gridSize := by positivity
  have xBounds := GridSegment.scaled_local_coordinate_endpoint_box positive factorNonnegative
    (offset := tagged.1.offset.1) ⟨sourceBounds.1,sourceBounds.2.1⟩ ⟨targetBounds.1,targetBounds.2.1⟩
  have yBounds := GridSegment.scaled_local_coordinate_endpoint_box positive factorNonnegative
    (offset := tagged.1.offset.2) ⟨sourceBounds.2.2.1,sourceBounds.2.2.2⟩ ⟨targetBounds.2.2.1,targetBounds.2.2.2⟩
  have box := GridSegment.realBoxContains_of_realContains contains
  simp only [GridSegment.RealBoxContains,GridSegment.scale,sourceEq,targetEq,Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add] at box
  have lowerX : (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.gridSize : ℝ)*(min 0 tagged.1.offset.1 : Int) ≤ point.1 := by
    apply le_trans _ box.1
    exact_mod_cast xBounds.1
  have upperX : point.1 ≤ (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.gridSize : ℝ)*((max 0 tagged.1.offset.1 : Int)+1) := by
    apply le_trans box.2.1
    exact_mod_cast xBounds.2
  have lowerY : (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.gridSize : ℝ)*(min 0 tagged.1.offset.2 : Int) ≤ point.2 := by
    apply le_trans _ box.2.2.1
    exact_mod_cast yBounds.1
  have upperY : point.2 ≤ (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.gridSize : ℝ)*((max 0 tagged.1.offset.2 : Int)+1) := by
    apply le_trans box.2.2.2
    exact_mod_cast yBounds.2
  apply refined_real_local_of_coordinate_box graph drawing (graphLocal _ (List.fst_mem_of_mem_zipIdx member))
  simpa only [paddedGridSize,Nat.cast_mul] using And.intro lowerX (And.intro upperX (And.intro lowerY upperY))

end LeanTrominoes.PeriodicGridDrawing
