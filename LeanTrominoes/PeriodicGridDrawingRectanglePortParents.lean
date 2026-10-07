/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortTransport
import LeanTrominoes.GridSegmentRealInteriorTransform

/-! # Each virtual rectangle port belongs properly to its original edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement GeneralVertexNormalization

def ColumnPortKey.parentKey {Vertex : Type*} : ColumnPortKey Vertex → Nat × Cell
  | .crossing key => key
  | .incidence tagged target => (tagged.2,endpointCell tagged target)

def RectanglePortKey.parentKey {Vertex : Type*} : RectanglePortKey Vertex → Nat × Cell
  | .vertical _ key => key.parentKey
  | .horizontal top key => (key.1,Cell.add key.2 (0,if top then 1 else 0))

theorem incidence_key_direction {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Int} {tagged : PeriodicEdge Vertex × Nat} {target right : Bool}
    (valid : (ColumnPortKey.incidence tagged target).Valid graph drawing column right) :
    if right then (drawing.outwardStraightSegment tagged target).finish.1 < (drawing.outwardStraightSegment tagged target).start.1 else
      (drawing.outwardStraightSegment tagged target).start.1 < (drawing.outwardStraightSegment tagged target).finish.1 := by
  have key := (outwardStraightSegment_key drawing tagged target).trans valid.2.2
  cases right <;> unfold GridSegment.straightRayKey at key <;> split_ifs at key <;> simp_all

theorem rectangle_vertical_port_parent {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (right : Bool) {key : ColumnPortKey Vertex}
    (valid : (RectanglePortKey.vertical right key).Valid graph drawing column) :
    (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).RealInteriorContains
      (((RectanglePortKey.vertical right key).virtualPort graph drawing column).shiftedPoint
        (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
        ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ)) := by
  have columnEqual : ((column+if right then 1 else 0 : Nat) : Int)-(if right then 1 else 0) = column := by
    cases right <;> simp
  cases key with
  | crossing key =>
    have point := virtualVerticalPort_point graph drawing ((column+if right then 1 else 0 : Nat) : Int) key right
    rw [columnEqual] at point
    change (drawing.liftedStraightSegment key.1 key.2).RealInteriorContains _
    dsimp only [RectanglePortKey.virtualPort,ColumnPortKey.virtualPort]
    rw [point]
    exact perturbedColumnHeight_realInteriorContains planar straight _ key
      (of_decide_eq_true (List.mem_filter.mp valid).2).1 right
  | incidence tagged target =>
    have sameX := valid.2.1
    have originColumn : (drawing.vertexPosition graph (endpointPort tagged target).vertex).1-(if right then 1 else 0) = column := by
      rw [← outwardStraightSegment_start planar.1.1 valid.1 target,sameX,columnEqual]
    have actual := virtualIncidencePort_realInteriorContains planar straight valid.1 target right (incidence_key_direction valid)
    rw [originColumn] at actual
    cases target
    · exact actual
    · exact (GridSegment.realInteriorContains_reverse _ _).mp actual

theorem rectangle_horizontal_port_point {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) {key : Nat × Cell} (sameSlab : seamAssignedSlab graph drawing key = column) (top : Bool) :
    (virtualHorizontalPort graph drawing (columnPerturbation graph drawing) key top).shiftedPoint
      (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) =
    ((shiftedSeamAbscissa graph drawing key : ℝ),(drawing.gridSize : ℝ)*(if top then 1 else 0)-(seamPerturbation graph drawing : ℝ)) := by
  cases top <;> apply Prod.ext <;>
    simp [virtualHorizontalPort,virtualSlabOrigin,RealRectangleBoundary.Port.shiftedPoint,RealRectangleBoundary.Port.point,sameSlab] <;> ring

theorem rectangle_horizontal_port_parent {Vertex : Type*} {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (column : Nat) (top : Bool) {key : Nat × Cell} (valid : (RectanglePortKey.horizontal top key).Valid graph drawing column) :
    (drawing.liftedStraightSegment (RectanglePortKey.horizontal (Vertex := Vertex) top key).parentKey.1
      (RectanglePortKey.horizontal (Vertex := Vertex) top key).parentKey.2).RealInteriorContains
      (((RectanglePortKey.horizontal top key).virtualPort graph drawing column).shiftedPoint
        (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
        ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ)) := by
  have actual := virtualHorizontalPort_realInteriorContains valid.1 (columnPerturbation graph drawing) false
  rw [virtualHorizontalPort_point] at actual
  change (drawing.liftedStraightSegment key.1 (Cell.add key.2 (0,if top then 1 else 0))).RealInteriorContains _
  dsimp only [RectanglePortKey.virtualPort]
  rw [rectangle_horizontal_port_point graph drawing column valid.2 top,liftedStraightSegment_add_cell]
  have shifted := (GridSegment.realInteriorContains_translate (drawing.liftedStraightSegment key.1 key.2)
    (drawing.periodTranslation (0,if top then 1 else 0)) ((shiftedSeamAbscissa graph drawing key : ℝ),((-seamPerturbation graph drawing : ℚ) : ℝ))).mpr actual
  cases top <;> simpa [periodTranslation,Cell.scale,Rat.cast_neg,sub_eq_add_neg,add_comm] using shifted

theorem rectanglePort_parent_realInteriorContains {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (drawing.liftedStraightSegment key.parentKey.1 key.parentKey.2).RealInteriorContains
      ((key.virtualPort graph drawing column).shiftedPoint
        (virtualSlabOrigin graph drawing (columnPerturbation graph drawing) column 0)
        ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ)) := by
  cases key with
  | vertical right key => exact rectangle_vertical_port_parent planar straight column right valid
  | horizontal top key => exact rectangle_horizontal_port_parent column top valid

end LeanTrominoes.PeriodicGridDrawing
