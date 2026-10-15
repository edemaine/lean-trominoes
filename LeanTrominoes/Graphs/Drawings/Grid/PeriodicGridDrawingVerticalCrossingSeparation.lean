/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedPeriodicVertexOrder
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossingOldSeparation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedCrossingRoutes
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalEnlargedCrossingColumnContacts
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisBox
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceWindow

/-! # Proper padded crossing bars avoid directly scaled vertical edges -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem scaled_vertical_segment_avoids_crossing_bar {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    {verticalEdge crossingEdge : PeriodicEdge Vertex × Nat}
    (verticalMember : verticalEdge ∈ graph.edges.zipIdx) (crossingMember : crossingEdge ∈ graph.edges.zipIdx)
    (verticalStraight : (drawing.edgeRoute verticalEdge.2).length = 2)
    (crossingStraight : (drawing.edgeRoute crossingEdge.2).length = 2)
    (verticalCell crossingCell : Cell)
    (vertical : (drawing.liftedStraightSegment verticalEdge.2 verticalCell).start.1 =
      (drawing.liftedStraightSegment verticalEdge.2 verticalCell).finish.1)
    {line : Int} (crosses : (drawing.liftedStraightSegment crossingEdge.2 crossingCell).CrossesVerticalLine line)
    {point : ℝ × ℝ}
    (verticalContains : ((drawing.liftedStraightSegment verticalEdge.2 verticalCell).scale
      (paddedRefinementFactor drawing.gridSize)).RealContains point)
    (barContains : GridPolyline.RealContains (paddedCrossingRoute graph drawing line (crossingEdge.2,crossingCell)) point) : False := by
  let segment := drawing.liftedStraightSegment verticalEdge.2 verticalCell
  let height := (drawing.liftedStraightSegment crossingEdge.2 crossingCell).rationalLineHeight line
  let output := paddedPeriodicColumnHeight graph drawing line height
  let factor : Int := paddedRefinementFactor drawing.gridSize
  have factorPositive : 0 < factor := by
    dsimp only [factor]
    exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have atColumn : point.1 = (factor : ℝ)*segment.start.1 := by
    obtain ⟨t,_,_,x,_⟩ := verticalContains
    simp only [GridSegment.scale,Cell.scale,Int.cast_mul,Int.cast_natCast] at x
    rw [← vertical] at x
    simpa only [factor,segment,Int.cast_natCast,sub_self,mul_zero,add_zero] using x
  have spacing : 10*(crossingBound drawing.gridSize : Int) < factor := by
    dsimp only [factor]
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have lineEq : line = segment.start.1 := enlargedCrossingBar_contact_scaled_column spacing barContains atColumn
  have pointY : point.2 = (output : ℝ) := (enlargedCrossingBar_real_bounds _ _ _ _ barContains).2
  have boundsY : min (factor*segment.start.2) (factor*segment.finish.2) ≤ output ∧
      output ≤ max (factor*segment.start.2) (factor*segment.finish.2) := by
    have box := ((GridSegment.realContains_iff_box_and_line _ _).mp verticalContains).1
    have bounds := box.2.2
    rw [pointY] at bounds
    simp only [GridSegment.scale,Cell.scale] at bounds
    exact_mod_cast bounds
  have crossing := periodic_crossing_residue_mem planar.1.1 crossingMember crossingStraight
    (graphLocal _ (List.fst_mem_of_mem_zipIdx crossingMember)) crossingCell crosses
  have sourcePosition : drawing.vertexPosition graph verticalEdge.1.source ∈ drawing.vertexPositions :=
    planar.1.1.vertexPosition_mem (port_vertex_mem planar.1.1.1 (sourcePort_mem_allPorts graph verticalMember))
  have targetPosition : drawing.vertexPosition graph verticalEdge.1.target ∈ drawing.vertexPositions :=
    planar.1.1.vertexPosition_mem (port_vertex_mem planar.1.1.1 (targetPort_mem_allPorts graph verticalMember))
  have sourceEq := liftedStraightSegment_start planar.1.1 verticalMember verticalCell
  have targetEq := liftedStraightSegment_finish planar.1.1 verticalMember verticalCell
  have sourceX : (Cell.add (drawing.vertexPosition graph verticalEdge.1.source) (drawing.periodTranslation verticalCell)).1 = line := by
    rw [← sourceEq]
    exact lineEq.symm
  have targetX : (Cell.add (drawing.vertexPosition graph verticalEdge.1.target)
      (drawing.periodTranslation (Cell.add verticalCell verticalEdge.1.offset))).1 = line := by
    rw [← targetEq,← vertical]
    exact lineEq.symm
  have belowSource : height < (segment.start.2 : ℚ) → output < factor*segment.start.2 := by
    intro below
    have gap := paddedPeriodicColumnHeight_below_lifted_vertex planar.1.1 degree crossing sourcePosition verticalCell sourceX
      (by rw [← sourceEq]; exact below)
    rw [← sourceEq] at gap
    exact gap
  have belowTarget : height < (segment.finish.2 : ℚ) → output < factor*segment.finish.2 := by
    intro below
    have gap := paddedPeriodicColumnHeight_below_lifted_vertex planar.1.1 degree crossing targetPosition
      (Cell.add verticalCell verticalEdge.1.offset) targetX
      (by rw [← targetEq]; exact below)
    rw [← targetEq] at gap
    exact gap
  have aboveSource : (segment.start.2 : ℚ) ≤ height → factor*segment.start.2 < output := by
    intro above
    have gap := paddedPeriodicColumnHeight_above_lifted_vertex planar.1.1 degree crossing sourcePosition verticalCell sourceX
      (by rw [← sourceEq]; exact above)
    rw [← sourceEq] at gap
    exact gap
  have aboveTarget : (segment.finish.2 : ℚ) ≤ height → factor*segment.finish.2 < output := by
    intro above
    have gap := paddedPeriodicColumnHeight_above_lifted_vertex planar.1.1 degree crossing targetPosition
      (Cell.add verticalCell verticalEdge.1.offset) targetX
      (by rw [← targetEq]; exact above)
    rw [← targetEq] at gap
    exact gap
  have oldBounds : min (segment.start.2 : ℚ) segment.finish.2 ≤ height ∧
      height ≤ max (segment.start.2 : ℚ) segment.finish.2 := by
    rcases le_total segment.start.2 segment.finish.2 with forward | backward
    · have scaled := mul_le_mul_of_nonneg_left forward factorPositive.le
      rw [min_eq_left scaled,max_eq_right scaled] at boundsY
      have castForward : (segment.start.2 : ℚ) ≤ segment.finish.2 := by exact_mod_cast forward
      rw [min_eq_left castForward,max_eq_right castForward]
      constructor
      · by_contra below
        have gap := belowSource (lt_of_not_ge below)
        omega
      · by_contra above
        have gap := aboveTarget (le_of_lt (lt_of_not_ge above))
        omega
    · have scaled := mul_le_mul_of_nonneg_left backward factorPositive.le
      rw [min_eq_right scaled,max_eq_left scaled] at boundsY
      have castBackward : (segment.finish.2 : ℚ) ≤ segment.start.2 := by exact_mod_cast backward
      rw [min_eq_right castBackward,max_eq_left castBackward]
      constructor
      · by_contra below
        have gap := belowTarget (lt_of_not_ge below)
        omega
      · by_contra above
        have gap := aboveSource (le_of_lt (lt_of_not_ge above))
        omega
  have oldVertical : segment.IsVertical := by
    refine ⟨vertical,?_⟩
    intro sameY
    exact liftedStraightSegment_nondegenerate planar.1 verticalMember verticalStraight verticalCell (Prod.ext vertical sameY)
  apply straight_vertical_avoids_crossing_point planar verticalMember crossingMember verticalStraight crossingStraight
    verticalCell crossingCell vertical crosses
  apply GridSegment.realContains_of_axis_box (Or.inr oldVertical)
  have sameX : segment.start.1 = segment.finish.1 := vertical
  simp only [GridSegment.RealBoxContains,← sameX,← lineEq,min_self,max_self]
  refine ⟨le_rfl,le_rfl,?_,?_⟩
  · exact_mod_cast oldBounds.1
  · exact_mod_cast oldBounds.2

end LeanTrominoes.PeriodicGridDrawing
