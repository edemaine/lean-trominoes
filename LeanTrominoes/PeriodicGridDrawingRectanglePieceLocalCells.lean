/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentLocalCellContact
import LeanTrominoes.PeriodicGridDrawingRectangleOriginalPortBounds
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.GridSegmentRealIntersection

/-! # A rectangle piece of a local straight edge lies in one of its endpoint cells -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing RationalIntegerStripCover

theorem rectangleParentChord_local_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (columnBound : column < drawing.gridSize) (cell : Cell)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column (tagged.2,Cell.scale (-1) cell) = some keys) :
    cell = (0,0) ∨ cell = tagged.1.offset := by
  have data := rectangleParentChord_data graph drawing column (tagged.2,Cell.scale (-1) cell) lookup
  have parameterBounds := (rectangleParentChord_parameter_bounds planar graphLocal straight column _ lookup).1
  have pointEq := rectanglePort_prototype_parameter_point planar graphLocal straight tagged.2 column cell data.1 data.2.2.1
  have oldContains := GridSegment.rationalPointAtParameter_realContains (drawing.liftedStraightSegment tagged.2 (0,0))
    parameterBounds.1.le parameterBounds.2.le
  rw [pointEq] at oldContains
  have box := GridSegment.realBoxContains_of_realContains oldContains
  have portBounds := rectanglePortOriginalPoint_bounds planar graphLocal straight column cell data.1
  have sourceEq := liftedStraightSegment_start planar.1.1 member (0,0)
  have targetEq := liftedStraightSegment_finish planar.1.1 member (0,0)
  have sourceMember := planar.1.1.vertexPosition_mem (port_vertex_mem planar.1.1.1 (sourcePort_mem_allPorts graph member))
  have targetMember := planar.1.1.vertexPosition_mem (port_vertex_mem planar.1.1.1 (targetPort_mem_allPorts graph member))
  have sourceBounds := planar.1.1.2.2.2.2.1 _ sourceMember
  have targetBounds := planar.1.1.2.2.2.2.1 _ targetMember
  change (0 < (drawing.vertexPosition graph tagged.1.source).1 ∧ _ ∧ _ ∧ _) at sourceBounds
  change (0 < (drawing.vertexPosition graph tagged.1.target).1 ∧ _ ∧ _ ∧ _) at targetBounds
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have xBox : (min (drawing.vertexPosition graph tagged.1.source).1
      ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*tagged.1.offset.1) : Int) ≤
        (rectanglePortOriginalPoint graph drawing column cell keys.1).1 ∧
      (rectanglePortOriginalPoint graph drawing column cell keys.1).1 ≤
        (max (drawing.vertexPosition graph tagged.1.source).1
          ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*tagged.1.offset.1) : Int) := by
    have bounds := And.intro box.1 box.2.1
    simp only [sourceEq,targetEq,Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add] at bounds
    exact_mod_cast bounds
  have yBox : (min (drawing.vertexPosition graph tagged.1.source).2
      ((drawing.vertexPosition graph tagged.1.target).2+(drawing.gridSize : Int)*tagged.1.offset.2) : Int) ≤
        (rectanglePortOriginalPoint graph drawing column cell keys.1).2 ∧
      (rectanglePortOriginalPoint graph drawing column cell keys.1).2 ≤
        (max (drawing.vertexPosition graph tagged.1.source).2
          ((drawing.vertexPosition graph tagged.1.target).2+(drawing.gridSize : Int)*tagged.1.offset.2) : Int) := by
    have bounds := box.2.2
    simp only [sourceEq,targetEq,Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add] at bounds
    exact_mod_cast bounds
  have globalX := GridSegment.local_coordinate_shifted_open_box positive
    ⟨sourceBounds.1,sourceBounds.2.1⟩ ⟨targetBounds.1,targetBounds.2.1⟩ (shift := 0) (by norm_num) xBox
  have globalY := GridSegment.local_coordinate_shifted_open_box positive
    ⟨sourceBounds.2.2.1,sourceBounds.2.2.2⟩ ⟨targetBounds.2.2.1,targetBounds.2.2.2⟩
    ⟨(seamPerturbation_positive graph drawing).le,seamPerturbation_lt_one graph drawing⟩ yBox
  have cellX : (drawing.gridSize : ℚ)*cell.1 ≤ (rectanglePortOriginalPoint graph drawing column cell keys.1).1 ∧
      (rectanglePortOriginalPoint graph drawing column cell keys.1).1 ≤ (drawing.gridSize : ℚ)*(cell.1+1) := by
    have epsilonPositive := columnPerturbation_positive planar straight
    have columnNonnegative : (0 : ℚ) ≤ column := by positivity
    have columnUpper : (column : ℚ)+1 ≤ drawing.gridSize := by exact_mod_cast (by omega : column+1 ≤ drawing.gridSize)
    unfold SlabContains at portBounds
    push_cast at portBounds
    constructor <;> linarith [portBounds.1.1,portBounds.1.2]
  have cellY : (drawing.gridSize : ℚ)*cell.2 ≤ (rectanglePortOriginalPoint graph drawing column cell keys.1).2+seamPerturbation graph drawing ∧
      (rectanglePortOriginalPoint graph drawing column cell keys.1).2+seamPerturbation graph drawing ≤ (drawing.gridSize : ℚ)*(cell.2+1) := by
    unfold RowContains at portBounds
    constructor <;> linarith [portBounds.2.1,portBounds.2.2]
  apply GridSegment.cell_eq_endpoint_of_local_coordinate_bounds
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member))
  · exact GridSegment.cell_index_bounds_of_overlap positive (by simpa only [add_zero] using globalX) cellX
  · exact GridSegment.cell_index_bounds_of_overlap positive globalY cellY

end LeanTrominoes.PeriodicGridDrawing
