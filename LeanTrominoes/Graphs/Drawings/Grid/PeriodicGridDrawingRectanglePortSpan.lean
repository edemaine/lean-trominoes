/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortParents
import LeanTrominoes.Common.Geometry.GridSegmentRealUnitColumnSpan

/-! # Every rectangle-port parent meets both rational column cuts properly -/
namespace LeanTrominoes.RealRectangleBoundary

theorem Port.point_x_bounds {width height : ℝ} {port : Port} (widthPositive : 0 < width) (inside : port.Inside width height) :
    (0 : ℝ) ≤ (port.point width height).1 ∧ (port.point width height).1 ≤ width := by
  obtain ⟨side,coordinate⟩ := port
  fin_cases side
  · simpa [Port.point] using widthPositive.le
  · change (0 : ℝ) ≤ coordinate ∧ coordinate ≤ width
    exact ⟨inside.1.le,by simpa [Port.extent] using inside.2.le⟩
  · simpa [Port.point] using widthPositive.le
  · change (0 : ℝ) ≤ coordinate ∧ coordinate ≤ width
    exact ⟨inside.1.le,by simpa [Port.extent] using inside.2.le⟩

end LeanTrominoes.RealRectangleBoundary
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectanglePort_parent_spans_unit_column {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).SpansUnitColumn column := by
  have contains := rectanglePort_parent_realInteriorContains planar straight column valid
  have inside := rectanglePort_virtual_inside planar graphLocal straight column valid
  have widthPositive : (0 : ℝ) < ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) := by
    exact_mod_cast virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have bounds := RealRectangleBoundary.Port.point_x_bounds widthPositive inside
  have positiveReal : (0 : ℝ) < columnPerturbation graph drawing := by exact_mod_cast columnPerturbation_positive planar straight
  have originX : (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0).1 =
      (column : ℝ)+(columnPerturbation graph drawing : ℝ) := by simp [virtualSlabOrigin]
  have widthEqual : ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) = 1-2*(columnPerturbation graph drawing : ℝ) := by push_cast; rfl
  apply GridSegment.realContains_spans_unit_column (GridSegment.realInteriorContains_implies_realContains contains)
  dsimp only [RealRectangleBoundary.Port.shiftedPoint,Prod.fst]
  rw [originX]
  simp only [Int.cast_natCast]
  rw [widthEqual] at bounds ⊢
  constructor <;> linarith [bounds.1,bounds.2]

theorem rectanglePort_parent_cut_realInteriorContains {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) (right : Bool) :
    (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).RealInteriorContains
      ((((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) : ℚ) : ℝ),
        ((drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).rationalHeightAt
          ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) : ℝ)) := by
  have small : columnPerturbation graph drawing < 1 :=
    lt_trans ((columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)) (by norm_num)
  simpa only [Int.cast_natCast] using GridSegment.rational_unit_column_cut_realInteriorContains
    (rectanglePort_parent_spans_unit_column planar graphLocal straight column valid) (columnPerturbation_positive planar straight) small right

end LeanTrominoes.PeriodicGridDrawing
