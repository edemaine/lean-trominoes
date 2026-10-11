/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendVerticalPorts

/-! # Vertical digital cores meet their endpoint fans only at their anchors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem vertical_coreRoute_sourceFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceSourceFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).start := by
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).start (sourcePort tagged.1 tagged.2) fanContains
  simp only [Int.cast_natCast] at bounds
  have box := coreRoute_box source drawing tagged coreContains
  have sign := cubicCore_y_sign source drawing tagged (vertical_direction_nonzero planar member vertical)
  have anchor := (vertical_fanAnchor_y planar degree member vertical).1
  have coordinate : ((cubicCore source drawing tagged).start.2 : ℝ) =
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*(subdivisionSegment source drawing tagged.1).start.2+
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(fanAnchor source drawing (sourcePort tagged.1 tagged.2)).2 := by
    simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,Int.cast_mul,Int.cast_add,Int.cast_natCast]
    ring
  rw [anchor] at coordinate
  have joint : Cell.add
      (Cell.scale ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
        (subdivisionSegment source drawing tagged.1).start)
      (Cell.scale (Cubic.rasterFactor drawing.gridSize) (fanAnchor source drawing (sourcePort tagged.1 tagged.2))) =
      (cubicCore source drawing tagged).start :=
    Option.some.inj ((fanAt_last source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
      (subdivisionSegment source drawing tagged.1).start (sourcePort tagged.1 tagged.2)).symm.trans
      (pieceSourceFan_last source drawing tagged))
  by_cases positive : 0 < (subdivisionSegment source drawing tagged.1).direction.2
  · rw [if_pos positive] at sign coordinate
    norm_num only [Int.cast_ofNat,Int.cast_neg] at coordinate
    have order : (cubicCore source drawing tagged).start.2 ≤ (cubicCore source drawing tagged).finish.2 := by
      simp only [GridSegment.direction] at sign
      omega
    simp only [GridSegment.RealBoxContains,min_eq_left order,max_eq_right order] at box
    have height : point.2 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
        (subdivisionSegment source drawing tagged.1).start.2+(Cubic.rasterFactor drawing.gridSize : ℝ)*10 := by
      have near := abs_le.mp bounds.2
      nlinarith [box.2.2.1]
    have contact := fanAt_vertical_boundary_contact planar degree (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).start
      (sourcePort_mem_allPorts _ member) true fanContains (by simpa only [ite_true,Int.cast_natCast] using height)
    exact contact.trans (congrArg realCell joint)
  · rw [if_neg positive] at sign coordinate
    norm_num only [Int.cast_ofNat,Int.cast_neg] at coordinate
    have order : (cubicCore source drawing tagged).finish.2 ≤ (cubicCore source drawing tagged).start.2 := by
      simp only [GridSegment.direction] at sign
      omega
    simp only [GridSegment.RealBoxContains,min_eq_right order,max_eq_left order] at box
    have height : point.2 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
        (subdivisionSegment source drawing tagged.1).start.2+(Cubic.rasterFactor drawing.gridSize : ℝ)*(-10) := by
      have near := abs_le.mp bounds.2
      nlinarith [box.2.2.2]
    have contact := fanAt_vertical_boundary_contact planar degree (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).start
      (sourcePort_mem_allPorts _ member) false fanContains (by simpa only [Bool.false_eq_true,ite_false,Int.cast_natCast] using height)
    exact contact.trans (congrArg realCell joint)

theorem vertical_coreRoute_targetFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceTargetFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).finish := by
  have original := (GridPolyline.realContains_reverse _ _).mp fanContains
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).finish (targetPort tagged.1 tagged.2) original
  simp only [Int.cast_natCast] at bounds
  have box := coreRoute_box source drawing tagged coreContains
  have sign := cubicCore_y_sign source drawing tagged (vertical_direction_nonzero planar member vertical)
  have anchor := (vertical_fanAnchor_y planar degree member vertical).2
  have coordinate : ((cubicCore source drawing tagged).finish.2 : ℝ) =
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*(subdivisionSegment source drawing tagged.1).finish.2+
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(fanAnchor source drawing (targetPort tagged.1 tagged.2)).2 := by
    simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,Int.cast_mul,Int.cast_add,Int.cast_natCast]
    ring
  rw [anchor] at coordinate
  have joint : Cell.add
      (Cell.scale ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
        (subdivisionSegment source drawing tagged.1).finish)
      (Cell.scale (Cubic.rasterFactor drawing.gridSize) (fanAnchor source drawing (targetPort tagged.1 tagged.2))) =
      (cubicCore source drawing tagged).finish := by
    have last := fanAt_last source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
      (subdivisionSegment source drawing tagged.1).finish (targetPort tagged.1 tagged.2)
    have head := pieceTargetFan_head source drawing tagged
    rw [pieceTargetFan,List.head?_reverse] at head
    exact Option.some.inj (last.symm.trans head)
  by_cases positive : 0 < (subdivisionSegment source drawing tagged.1).direction.2
  · rw [if_pos positive] at sign coordinate
    norm_num only [Int.cast_ofNat,Int.cast_neg] at coordinate
    have order : (cubicCore source drawing tagged).start.2 ≤ (cubicCore source drawing tagged).finish.2 := by
      simp only [GridSegment.direction] at sign
      omega
    simp only [GridSegment.RealBoxContains,min_eq_left order,max_eq_right order] at box
    have height : point.2 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
        (subdivisionSegment source drawing tagged.1).finish.2+(Cubic.rasterFactor drawing.gridSize : ℝ)*(-10) := by
      have near := abs_le.mp bounds.2
      nlinarith [box.2.2.2]
    have contact := fanAt_vertical_boundary_contact planar degree (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).finish
      (targetPort_mem_allPorts _ member) false original (by simpa only [Bool.false_eq_true,ite_false,Int.cast_natCast] using height)
    exact contact.trans (congrArg realCell joint)
  · rw [if_neg positive] at sign coordinate
    norm_num only [Int.cast_ofNat,Int.cast_neg] at coordinate
    have order : (cubicCore source drawing tagged).finish.2 ≤ (cubicCore source drawing tagged).start.2 := by
      simp only [GridSegment.direction] at sign
      omega
    simp only [GridSegment.RealBoxContains,min_eq_right order,max_eq_left order] at box
    have height : point.2 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*
        (subdivisionSegment source drawing tagged.1).finish.2+(Cubic.rasterFactor drawing.gridSize : ℝ)*10 := by
      have near := abs_le.mp bounds.2
      nlinarith [box.2.2.1]
    have contact := fanAt_vertical_boundary_contact planar degree (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).finish
      (targetPort_mem_allPorts _ member) true original (by simpa only [ite_true,Int.cast_natCast] using height)
    exact contact.trans (congrArg realCell joint)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
