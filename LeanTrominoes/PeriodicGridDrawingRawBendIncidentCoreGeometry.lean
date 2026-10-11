/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentCoreData
import LeanTrominoes.PeriodicGridDrawingRawBendDigitalCores

/-! # Orientation-independent half planes of incident cores -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem right_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (right : 0 < raw.direction.1) {point : ℝ × ℝ}
    (box : (core.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point) :
    (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*raw.start.1+
      5*Cubic.rasterFactor drawing.gridSize ≤ point.1 := by
  have slope := GridSegment.perturbed_right_core_slope data.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) right data.bounds.2
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have sign : 0 < (core.scale (Cubic.rasterFactor drawing.gridSize)).direction.1 := by
    simp only [GridSegment.direction_scale,Cell.scale]
    exact mul_pos rasterPositive slope.1
  have ordered : (core.scale (Cubic.rasterFactor drawing.gridSize)).start.1 ≤
      (core.scale (Cubic.rasterFactor drawing.gridSize)).finish.1 := by simp only [GridSegment.direction] at sign; omega
  have anchor := fanAnchor_x planar degree data.member
  simp only [data.right_key right,BendFan.horizontalSign,mul_one] at anchor
  have bound := box.1
  rw [min_eq_left ordered] at bound
  simp only [GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat] at bound
  nlinarith

theorem left_bound {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (left : raw.direction.1 < 0) {point : ℝ × ℝ}
    (box : (core.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point) :
    point.1 ≤ (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*raw.start.1-
      5*Cubic.rasterFactor drawing.gridSize := by
  have slope := GridSegment.perturbed_left_core_slope data.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) left data.bounds.2
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have sign : (core.scale (Cubic.rasterFactor drawing.gridSize)).direction.1 < 0 := by
    simp only [GridSegment.direction_scale,Cell.scale]
    exact mul_neg_of_pos_of_neg rasterPositive slope.1
  have ordered : (core.scale (Cubic.rasterFactor drawing.gridSize)).finish.1 ≤
      (core.scale (Cubic.rasterFactor drawing.gridSize)).start.1 := by simp only [GridSegment.direction] at sign; omega
  have anchor := fanAnchor_x planar degree data.member
  simp only [data.left_key left,BendFan.horizontalSign,mul_neg_one] at anchor
  have bound := box.2.1
  rw [max_eq_left ordered] at bound
  simp only [GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
    Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg] at bound
  nlinarith

theorem vertical_x {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (vertical : raw.direction.1 = 0) {point : ℝ × ℝ}
    (box : (core.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point) :
    point.1 = (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*raw.start.1 := by
  have anchor := fanAnchor_x planar degree data.member
  rw [data.vertical_key vertical] at anchor
  split_ifs at anchor <;> simp only [BendFan.horizontalSign,mul_zero] at anchor
  all_goals
    have equalX : (core.scale (Cubic.rasterFactor drawing.gridSize)).start.1 =
        (core.scale (Cubic.rasterFactor drawing.gridSize)).finish.1 := by
      simp only [GridSegment.scale,Cell.scale,data.vertical vertical]
    have lower := box.1
    have upper := box.2.1
    rw [← equalX,min_self] at lower
    rw [← equalX,max_self] at upper
    simp only [GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
      Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_zero,add_zero] at lower upper
    nlinarith

theorem vertical_y {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (vertical : raw.direction.1 = 0) {point : ℝ × ℝ}
    (box : (core.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point) :
    if 0 < raw.direction.2 then
      (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*raw.start.2+
        10*Cubic.rasterFactor drawing.gridSize ≤ point.2
    else point.2 ≤ (Cubic.rasterFactor drawing.gridSize : ℝ)*(Cubic.coreFactor drawing.gridSize : ℝ)*raw.start.2-
      10*Cubic.rasterFactor drawing.gridSize := by
  have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize
  have sign := GridSegment.bounded_coordinate_sign data.perturbed.direction.2 (by norm_num) (by omega)
    (data.vertical_direction_nonzero vertical)
  have key := data.vertical_key vertical
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  split_ifs with up
  · rw [if_pos up] at sign key
    have anchor := fanAnchor_vertical_y planar degree data.member true key
    simp only [ite_true] at anchor
    have scaledSign : 0 < (core.scale (Cubic.rasterFactor drawing.gridSize)).direction.2 := by
      simp only [GridSegment.direction_scale,Cell.scale]
      exact mul_pos rasterPositive sign
    have ordered : (core.scale (Cubic.rasterFactor drawing.gridSize)).start.2 ≤
        (core.scale (Cubic.rasterFactor drawing.gridSize)).finish.2 := by simp only [GridSegment.direction] at scaledSign; omega
    have bound := box.2.2.1
    rw [min_eq_left ordered] at bound
    simp only [GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
      Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat] at bound
    nlinarith
  · rw [if_neg up] at sign key
    have anchor := fanAnchor_vertical_y planar degree data.member false key
    simp only [Bool.false_eq_true,ite_false] at anchor
    have scaledSign : (core.scale (Cubic.rasterFactor drawing.gridSize)).direction.2 < 0 := by
      simp only [GridSegment.direction_scale,Cell.scale]
      exact mul_neg_of_pos_of_neg rasterPositive sign
    have ordered : (core.scale (Cubic.rasterFactor drawing.gridSize)).finish.2 ≤
        (core.scale (Cubic.rasterFactor drawing.gridSize)).start.2 := by simp only [GridSegment.direction] at scaledSign; omega
    have bound := box.2.2.2
    rw [max_eq_left ordered] at bound
    simp only [GridSegment.scale,Cell.scale,data.start,Cell.add,anchor,
      Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg] at bound
    nlinarith

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
