/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendHorizontalPorts
import LeanTrominoes.PeriodicGridDrawingRawBendVerticalPorts

/-! # Digital cores remain beyond the sides of their source rectangles -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem coreRoute_horizontal_source_halfPlane {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    0 ≤ (coreSide source drawing tagged : ℝ)*(point.1-(cubicCore source drawing tagged).start.1) := by
  have fullBox := coreRoute_box source drawing tagged contains
  have box := And.intro fullBox.1 fullBox.2.1
  have width := cubicCore_horizontal_width source drawing tagged horizontal
  rcases coreSide_unit source drawing tagged with side | side
  · rw [side] at width ⊢
    have ordered : (cubicCore source drawing tagged).start.1 ≤ (cubicCore source drawing tagged).finish.1 := by omega
    simp only [min_eq_left ordered,max_eq_right ordered] at box
    norm_num
    linarith [box.1]
  · rw [side] at width ⊢
    have ordered : (cubicCore source drawing tagged).finish.1 ≤ (cubicCore source drawing tagged).start.1 := by omega
    simp only [min_eq_right ordered,max_eq_left ordered] at box
    norm_num
    linarith [box.2]

theorem coreRoute_right_source_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (right : 0 < (subdivisionSegment source drawing tagged.1).direction.1) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
      (subdivisionSegment source drawing tagged.1).start.1+5*Cubic.rasterFactor drawing.gridSize ≤ point.1 := by
  have bound := coreRoute_horizontal_source_halfPlane source drawing tagged (ne_of_gt right) contains
  have anchor := (horizontal_fanAnchor_x planar degree member (ne_of_gt right)).1
  simp only [coreSide,if_pos right] at bound anchor
  simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_one,mul_one] at bound
  nlinarith

theorem coreRoute_left_source_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (left : (subdivisionSegment source drawing tagged.1).direction.1 < 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    point.1 ≤ (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
      (subdivisionSegment source drawing tagged.1).start.1-5*Cubic.rasterFactor drawing.gridSize := by
  have bound := coreRoute_horizontal_source_halfPlane source drawing tagged (ne_of_lt left) contains
  have anchor := (horizontal_fanAnchor_x planar degree member (ne_of_lt left)).1
  simp only [coreSide,if_neg (not_lt_of_ge left.le)] at bound anchor
  simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg,Int.cast_one] at bound
  nlinarith

theorem coreRoute_vertical_x {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    point.1 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
      (subdivisionSegment source drawing tagged.1).start.1 := by
  have sameX : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1 := by
    simp only [GridSegment.direction] at vertical
    omega
  have anchors := vertical_anchoredSegment_x planar degree (Cubic.coreFactor drawing.gridSize) member sameX
  have fullBox := coreRoute_box source drawing tagged contains
  have box := And.intro fullBox.1 fullBox.2.1
  have coreX : (cubicCore source drawing tagged).start.1 = (cubicCore source drawing tagged).finish.1 := by
    simp only [cubicCore,GridSegment.scale,Cell.scale,anchors.1,anchors.2,sameX]
  simp only [← coreX,min_self,max_self] at box
  have equal : point.1 = (cubicCore source drawing tagged).start.1 := le_antisymm box.2 box.1
  rw [equal]
  simp only [cubicCore,GridSegment.scale,Cell.scale,anchors.1,Int.cast_mul,Int.cast_natCast]
  ring

theorem coreRoute_up_source_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0)
    (up : 0 < (subdivisionSegment source drawing tagged.1).direction.2) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
      (subdivisionSegment source drawing tagged.1).start.2+10*Cubic.rasterFactor drawing.gridSize ≤ point.2 := by
  have sign := cubicCore_y_sign source drawing tagged (ne_of_gt up)
  rw [if_pos up] at sign
  have ordered : (cubicCore source drawing tagged).start.2 ≤ (cubicCore source drawing tagged).finish.2 := by
    simp only [GridSegment.direction] at sign
    omega
  have box := (coreRoute_box source drawing tagged contains).2.2
  simp only [min_eq_left ordered,max_eq_right ordered] at box
  have anchor := (vertical_fanAnchor_y planar degree member vertical).1
  rw [if_pos up] at anchor
  have bound := box.1
  simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat] at bound
  nlinarith

theorem coreRoute_down_source_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0)
    (down : (subdivisionSegment source drawing tagged.1).direction.2 < 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (coreRoute source drawing tagged) point) :
    point.2 ≤ (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
      (subdivisionSegment source drawing tagged.1).start.2-10*Cubic.rasterFactor drawing.gridSize := by
  have sign := cubicCore_y_sign source drawing tagged (ne_of_lt down)
  rw [if_neg (not_lt_of_ge down.le)] at sign
  have ordered : (cubicCore source drawing tagged).finish.2 ≤ (cubicCore source drawing tagged).start.2 := by
    simp only [GridSegment.direction] at sign
    omega
  have box := (coreRoute_box source drawing tagged contains).2.2
  simp only [min_eq_right ordered,max_eq_left ordered] at box
  have anchor := (vertical_fanAnchor_y planar degree member vertical).1
  rw [if_neg (not_lt_of_ge down.le)] at anchor
  have bound := box.2
  simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg] at bound
  nlinarith

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
