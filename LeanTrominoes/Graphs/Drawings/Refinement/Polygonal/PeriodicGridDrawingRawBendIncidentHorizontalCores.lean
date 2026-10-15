/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendPortSpacing
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendHorizontalPorts
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendOrderedRightCores
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendOrderedLeftCores
import LeanTrominoes.Common.Geometry.GridSegmentRationalSlopeOrder

/-! # Actual incident horizontal cores are disjoint

These statements use the original graph incidences, without requiring
separate assumptions about anchor positions or integer cross products.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem right_source_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstRight : 0 < (subdivisionSegment source drawing first.1).direction.1)
    (secondRight : 0 < (subdivisionSegment source drawing second.1).direction.1)
    (sameVertex : first.1.source = second.1.source)
    (different : sourcePort first.1 first.2 ≠ sourcePort second.1 second.2)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (coreRoute source drawing first) point) :
    ¬GridPolyline.RealContains (coreRoute source drawing second) point := by
  intro secondContains
  have firstPortMember := sourcePort_mem_allPorts _ firstMember
  have secondPortMember := sourcePort_mem_allPorts _ secondMember
  have samePortVertex : (sourcePort first.1 first.2).vertex = (sourcePort second.1 second.2).vertex := sameVertex
  have firstKey : (shiftedDrawing source drawing).portRayKey (sourcePort first.1 first.2) =
      .right (subdivisionSegment source drawing first.1).rationalSlope := by
    rw [shifted_source_portRayKey source drawing firstMember,GridSegment.straightRayKey_of_right firstRight]
  have secondKey : (shiftedDrawing source drawing).portRayKey (sourcePort second.1 second.2) =
      .right (subdivisionSegment source drawing second.1).rationalSlope := by
    rw [shifted_source_portRayKey source drawing secondMember,GridSegment.straightRayKey_of_right secondRight]
  have slopesNe : (subdivisionSegment source drawing first.1).rationalSlope ≠
      (subdivisionSegment source drawing second.1).rationalSlope := by
    intro equal
    exact different (shifted_distinctPortRayKeys planar _ firstPortMember _ secondPortMember samePortVertex
      (by rw [firstKey,secondKey,equal]))
  have firstAnchor := (horizontal_fanAnchor_x planar degree firstMember (ne_of_gt firstRight)).1
  have secondAnchor := (horizontal_fanAnchor_x planar degree secondMember (ne_of_gt secondRight)).1
  simp only [coreSide,if_pos firstRight] at firstAnchor
  simp only [coreSide,if_pos secondRight] at secondAnchor
  have sameColumn : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.1 =
      (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.1 := by
    simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex,firstAnchor,secondAnchor]
  rcases lt_or_gt_of_ne slopesNe with ordered | ordered
  · have gap := fanAnchor_right_gap planar degree firstPortMember secondPortMember samePortVertex firstKey secondKey ordered
    have ports : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.2+2 ≤
        (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.2 := by
      simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex]
      omega
    exact ordered_right_coreRoutes_disjoint planar graphLocal drawingLocal firstMember secondMember firstRight secondRight
      sameColumn ports ((GridSegment.cross_positive_iff_right_slope_order firstRight secondRight).mpr ordered)
      firstContains secondContains
  · have gap := fanAnchor_right_gap planar degree secondPortMember firstPortMember samePortVertex.symm secondKey firstKey ordered
    have ports : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.2+2 ≤
        (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.2 := by
      simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex]
      omega
    exact ordered_right_coreRoutes_disjoint planar graphLocal drawingLocal secondMember firstMember secondRight firstRight
      sameColumn.symm ports ((GridSegment.cross_positive_iff_right_slope_order secondRight firstRight).mpr ordered)
      secondContains firstContains

theorem left_source_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstLeft : (subdivisionSegment source drawing first.1).direction.1 < 0)
    (secondLeft : (subdivisionSegment source drawing second.1).direction.1 < 0)
    (sameVertex : first.1.source = second.1.source)
    (different : sourcePort first.1 first.2 ≠ sourcePort second.1 second.2)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (coreRoute source drawing first) point) :
    ¬GridPolyline.RealContains (coreRoute source drawing second) point := by
  intro secondContains
  have firstPortMember := sourcePort_mem_allPorts _ firstMember
  have secondPortMember := sourcePort_mem_allPorts _ secondMember
  have samePortVertex : (sourcePort first.1 first.2).vertex = (sourcePort second.1 second.2).vertex := sameVertex
  have firstKey : (shiftedDrawing source drawing).portRayKey (sourcePort first.1 first.2) =
      .left (subdivisionSegment source drawing first.1).rationalSlope := by
    rw [shifted_source_portRayKey source drawing firstMember,GridSegment.straightRayKey_of_left firstLeft]
  have secondKey : (shiftedDrawing source drawing).portRayKey (sourcePort second.1 second.2) =
      .left (subdivisionSegment source drawing second.1).rationalSlope := by
    rw [shifted_source_portRayKey source drawing secondMember,GridSegment.straightRayKey_of_left secondLeft]
  have slopesNe : (subdivisionSegment source drawing first.1).rationalSlope ≠
      (subdivisionSegment source drawing second.1).rationalSlope := by
    intro equal
    exact different (shifted_distinctPortRayKeys planar _ firstPortMember _ secondPortMember samePortVertex
      (by rw [firstKey,secondKey,equal]))
  have firstAnchor := (horizontal_fanAnchor_x planar degree firstMember (ne_of_lt firstLeft)).1
  have secondAnchor := (horizontal_fanAnchor_x planar degree secondMember (ne_of_lt secondLeft)).1
  simp only [coreSide,if_neg (not_lt_of_ge firstLeft.le)] at firstAnchor
  simp only [coreSide,if_neg (not_lt_of_ge secondLeft.le)] at secondAnchor
  have sameColumn : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.1 =
      (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.1 := by
    simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex,firstAnchor,secondAnchor]
  have crossSwap : GridSegment.cross (subdivisionSegment source drawing first.1).direction
      (subdivisionSegment source drawing second.1).direction =
      -GridSegment.cross (subdivisionSegment source drawing second.1).direction
        (subdivisionSegment source drawing first.1).direction := by
    simp only [GridSegment.cross]
    ring
  rcases lt_or_gt_of_ne slopesNe with ordered | ordered
  · have gap := fanAnchor_left_gap planar degree firstPortMember secondPortMember samePortVertex firstKey secondKey ordered
    have ports : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.2+2 ≤
        (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.2 := by
      simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex]
      omega
    have positive := (GridSegment.cross_positive_iff_left_slope_order firstLeft secondLeft).mpr ordered
    have negative : GridSegment.cross (subdivisionSegment source drawing second.1).direction
        (subdivisionSegment source drawing first.1).direction < 0 := by omega
    exact ordered_left_coreRoutes_disjoint planar graphLocal drawingLocal secondMember firstMember secondLeft firstLeft
      sameColumn.symm ports negative secondContains firstContains
  · have gap := fanAnchor_left_gap planar degree secondPortMember firstPortMember samePortVertex.symm secondKey firstKey ordered
    have ports : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.2+2 ≤
        (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.2 := by
      simp only [anchoredSegment,Cell.add,Cell.scale,subdivisionSegment,sameVertex]
      omega
    have positive := (GridSegment.cross_positive_iff_left_slope_order secondLeft firstLeft).mpr ordered
    have negative : GridSegment.cross (subdivisionSegment source drawing first.1).direction
        (subdivisionSegment source drawing second.1).direction < 0 := by omega
    exact ordered_left_coreRoutes_disjoint planar graphLocal drawingLocal firstMember secondMember firstLeft secondLeft
      sameColumn ports negative firstContains secondContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
