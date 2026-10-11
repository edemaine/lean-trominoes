/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPieceRoutes

/-! # Horizontal cores leave their assigned fan sides

The source anchor lies on the outward horizontal side and the target anchor
on the opposite side. Together with endpoint steps this isolates each core
from its own endpoint fans, including bends on fundamental-cell boundaries.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem horizontal_fanAnchor_x {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) :
    (fanAnchor source drawing (sourcePort tagged.1 tagged.2)).1 = 5*coreSide source drawing tagged ∧
      (fanAnchor source drawing (targetPort tagged.1 tagged.2)).1 = -5*coreSide source drawing tagged := by
  have first := fanAnchor_x planar degree (sourcePort_mem_allPorts _ member)
  have last := fanAnchor_x planar degree (targetPort_mem_allPorts _ member)
  rw [shifted_source_portRayKey source drawing member] at first
  rw [shifted_target_portRayKey source drawing member] at last
  by_cases positive : 0 < (subdivisionSegment source drawing tagged.1).direction.1
  · have right : (subdivisionSegment source drawing tagged.1).start.1 < (subdivisionSegment source drawing tagged.1).finish.1 := by
      simp only [GridSegment.direction] at positive
      omega
    have notLeft : ¬(subdivisionSegment source drawing tagged.1).finish.1 < (subdivisionSegment source drawing tagged.1).start.1 := by omega
    simpa [GridSegment.straightRayKey,GridSegment.reverse,right,notLeft,
      BendFan.horizontalSign,coreSide,positive] using And.intro first last
  · have left : (subdivisionSegment source drawing tagged.1).finish.1 < (subdivisionSegment source drawing tagged.1).start.1 := by
      simp only [GridSegment.direction] at horizontal positive
      omega
    have notRight : ¬(subdivisionSegment source drawing tagged.1).start.1 < (subdivisionSegment source drawing tagged.1).finish.1 := by omega
    simpa [GridSegment.straightRayKey,GridSegment.reverse,left,notRight,
      BendFan.horizontalSign,coreSide,positive] using And.intro first last

theorem pieceSourceFan_horizontal_side {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (pieceSourceFan source drawing tagged) point) :
    (coreSide source drawing tagged : ℝ)*(point.1-(cubicCore source drawing tagged).start.1) ≤ 0 := by
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).start (sourcePort tagged.1 tagged.2) contains
  simp only [Int.cast_natCast] at bounds
  have anchor := (horizontal_fanAnchor_x planar degree member horizontal).1
  have coordinate : (cubicCore source drawing tagged).start.1 =
      (Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int)*(subdivisionSegment source drawing tagged.1).start.1+
      (Cubic.rasterFactor drawing.gridSize : Int)*(5*coreSide source drawing tagged) := by
    simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor]
    ring
  rw [coordinate]
  push_cast
  rcases coreSide_unit source drawing tagged with side | side <;>
    rw [side] <;> norm_num <;> have bounded := abs_le.mp bounds.1 <;> nlinarith

theorem pieceTargetFan_horizontal_side {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (pieceTargetFan source drawing tagged) point) :
    (coreSide source drawing tagged : ℝ)*((cubicCore source drawing tagged).finish.1-point.1) ≤ 0 := by
  have original := (GridPolyline.realContains_reverse _ _).mp contains
  have bounds := fanAt_real_bounds source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).finish (targetPort tagged.1 tagged.2) original
  simp only [Int.cast_natCast] at bounds
  have anchor := (horizontal_fanAnchor_x planar degree member horizontal).2
  have coordinate : (cubicCore source drawing tagged).finish.1 =
      (Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int)*(subdivisionSegment source drawing tagged.1).finish.1+
      (Cubic.rasterFactor drawing.gridSize : Int)*(-5*coreSide source drawing tagged) := by
    simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale,anchor]
    ring
  rw [coordinate]
  push_cast
  rcases coreSide_unit source drawing tagged with side | side <;>
    rw [side] <;> norm_num <;> have bounded := abs_le.mp bounds.1 <;> nlinarith

theorem horizontal_coreRoute_sourceFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceSourceFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).start := by
  simp only [coreRoute,if_neg horizontal] at coreContains
  exact GridSegment.kickedDigitalRoute_source_fan_contacts (coreSide_unit source drawing tagged)
    (cubicCore_horizontal_width source drawing tagged horizontal)
    (fun _ contains => pieceSourceFan_horizontal_side planar degree member horizontal contains) coreContains fanContains

theorem horizontal_coreRoute_targetFan_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (horizontal : (subdivisionSegment source drawing tagged.1).direction.1 ≠ 0) {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (coreRoute source drawing tagged) point)
    (fanContains : GridPolyline.RealContains (pieceTargetFan source drawing tagged) point) :
    point = realCell (cubicCore source drawing tagged).finish := by
  simp only [coreRoute,if_neg horizontal] at coreContains
  exact GridSegment.kickedDigitalRoute_target_fan_contacts (coreSide_unit source drawing tagged)
    (cubicCore_horizontal_width source drawing tagged horizontal)
    (fun _ contains => pieceTargetFan_horizontal_side planar degree member horizontal contains) coreContains fanContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
