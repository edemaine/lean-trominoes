/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendVerticalFanPlacement
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendPieceRoutes

/-! # Vertical core directions and their two fan anchors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem vertical_direction_nonzero {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) :
    (subdivisionSegment source drawing tagged.1).direction.2 ≠ 0 := by
  intro zero
  apply subdivision_segment_nonconstant planar member
  simp only [GridSegment.direction] at vertical zero
  apply Prod.ext <;> omega

theorem cubicCore_y_sign {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (nonzero : (subdivisionSegment source drawing tagged.1).direction.2 ≠ 0) :
    if 0 < (subdivisionSegment source drawing tagged.1).direction.2 then
      0 < (cubicCore source drawing tagged).direction.2 else (cubicCore source drawing tagged).direction.2 < 0 := by
  have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize
  have sign := GridSegment.bounded_coordinate_sign
    (anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) tagged).direction.2
    (by norm_num) (by omega) nonzero
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  simp only [cubicCore,GridSegment.direction_scale,Cell.scale]
  split_ifs with up
  · rw [if_pos up] at sign
    exact mul_pos rasterPositive sign
  · rw [if_neg up] at sign
    exact mul_neg_of_pos_of_neg rasterPositive sign

theorem vertical_fanAnchor_y {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) :
    (fanAnchor source drawing (sourcePort tagged.1 tagged.2)).2 =
      (if 0 < (subdivisionSegment source drawing tagged.1).direction.2 then 10 else -10) ∧
    (fanAnchor source drawing (targetPort tagged.1 tagged.2)).2 =
      (if 0 < (subdivisionSegment source drawing tagged.1).direction.2 then -10 else 10) := by
  have sameX : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1 := by
    simp only [GridSegment.direction] at vertical
    omega
  have nonzero := vertical_direction_nonzero planar member vertical
  by_cases positive : 0 < (subdivisionSegment source drawing tagged.1).direction.2
  · have up : (subdivisionSegment source drawing tagged.1).start.2 < (subdivisionSegment source drawing tagged.1).finish.2 := by
      simp only [GridSegment.direction] at positive
      omega
    have notDown : ¬(subdivisionSegment source drawing tagged.1).finish.2 < (subdivisionSegment source drawing tagged.1).start.2 := by omega
    have sourceKey : (shiftedDrawing source drawing).portRayKey (sourcePort tagged.1 tagged.2) = .up := by
      rw [shifted_source_portRayKey source drawing member]
      simp [GridSegment.straightRayKey,sameX,up]
    have targetKey : (shiftedDrawing source drawing).portRayKey (targetPort tagged.1 tagged.2) = .down := by
      rw [shifted_target_portRayKey source drawing member]
      simp [GridSegment.straightRayKey,GridSegment.reverse,sameX,notDown]
    have first := fanAnchor_vertical_y planar degree (sourcePort_mem_allPorts _ member) true sourceKey
    have last := fanAnchor_vertical_y planar degree (targetPort_mem_allPorts _ member) false targetKey
    simpa only [if_pos positive,ite_true,Bool.false_eq_true,ite_false] using And.intro first last
  · have down : (subdivisionSegment source drawing tagged.1).finish.2 < (subdivisionSegment source drawing tagged.1).start.2 := by
      simp only [GridSegment.direction] at positive nonzero
      omega
    have notUp : ¬(subdivisionSegment source drawing tagged.1).start.2 < (subdivisionSegment source drawing tagged.1).finish.2 := by omega
    have sourceKey : (shiftedDrawing source drawing).portRayKey (sourcePort tagged.1 tagged.2) = .down := by
      rw [shifted_source_portRayKey source drawing member]
      simp [GridSegment.straightRayKey,sameX,notUp]
    have targetKey : (shiftedDrawing source drawing).portRayKey (targetPort tagged.1 tagged.2) = .up := by
      rw [shifted_target_portRayKey source drawing member]
      simp [GridSegment.straightRayKey,GridSegment.reverse,sameX,down]
    have first := fanAnchor_vertical_y planar degree (sourcePort_mem_allPorts _ member) false sourceKey
    have last := fanAnchor_vertical_y planar degree (targetPort_mem_allPorts _ member) true targetKey
    simpa only [if_neg positive,ite_true,Bool.false_eq_true,ite_false] using And.intro first last

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
