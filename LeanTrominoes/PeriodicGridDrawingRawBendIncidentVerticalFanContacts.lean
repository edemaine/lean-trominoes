/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentCoreGeometry
import LeanTrominoes.PeriodicGridDrawingRawBendFanPlacement

/-! # A vertical core can touch any incident fan only at its own anchor -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem vertical_fan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (vertical : raw.direction.1 = 0) (otherPort : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (box : (core.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point)
    (fanContains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) raw.start otherPort) point) :
    point = realCell (core.scale (Cubic.rasterFactor drawing.gridSize)).start := by
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    raw.start otherPort fanContains
  simp only [Int.cast_natCast] at bounds
  have x := data.vertical_x planar degree vertical box
  have y := data.vertical_y planar degree vertical box
  have key := data.vertical_key vertical
  have anchorX := fanAnchor_x planar degree data.member
  rw [key] at anchorX
  have zeroX : (fanAnchor source drawing port).1 = 0 := by
    split_ifs at anchorX <;> simpa only [BendFan.horizontalSign,mul_zero] using anchorX
  apply Prod.ext
  · simp only [realCell,GridSegment.scale,Cell.scale,data.start,Cell.add,zeroX,add_zero,Int.cast_mul,Int.cast_natCast]
    nlinarith
  · by_cases up : 0 < raw.direction.2
    · rw [if_pos up] at y key
      have anchorY := fanAnchor_vertical_y planar degree data.member true key
      simp only [ite_true] at anchorY
      simp only [realCell,GridSegment.scale,Cell.scale,data.start,Cell.add,anchorY,
        Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat]
      have upper := (abs_le.mp bounds.2).2
      nlinarith
    · rw [if_neg up] at y key
      have anchorY := fanAnchor_vertical_y planar degree data.member false key
      simp only [Bool.false_eq_true,ite_false] at anchorY
      simp only [realCell,GridSegment.scale,Cell.scale,data.start,Cell.add,anchorY,
        Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_neg]
      have lower := (abs_le.mp bounds.2).1
      nlinarith

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
