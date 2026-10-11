/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentHorizontalCores
import LeanTrominoes.PeriodicGridDrawingRawBendCoreHalfPlanes

/-! # All distinct cores leaving a common source vertex are disjoint -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem vertical_source_portRayKey {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (vertical : (subdivisionSegment source drawing tagged.1).direction.1 = 0) :
    (shiftedDrawing source drawing).portRayKey (sourcePort tagged.1 tagged.2) =
      if 0 < (subdivisionSegment source drawing tagged.1).direction.2 then .up else .down := by
  rw [shifted_source_portRayKey source drawing member]
  have sameX : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1 := by
    simp only [GridSegment.direction] at vertical
    omega
  have yOrder : (subdivisionSegment source drawing tagged.1).start.2 < (subdivisionSegment source drawing tagged.1).finish.2 ↔
      0 < (subdivisionSegment source drawing tagged.1).direction.2 := by
    simp only [GridSegment.direction]
    omega
  simp only [GridSegment.straightRayKey,sameX,lt_self_iff_false,ite_false,yOrder]

theorem source_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (sameVertex : first.1.source = second.1.source)
    (different : sourcePort first.1 first.2 ≠ sourcePort second.1 second.2)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (coreRoute source drawing first) point) :
    ¬GridPolyline.RealContains (coreRoute source drawing second) point := by
  intro secondContains
  have rasterPositive : (0 : ℝ) < Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have sameX : (subdivisionSegment source drawing first.1).start.1 = (subdivisionSegment source drawing second.1).start.1 := by
    simp only [subdivisionSegment,sameVertex]
  have sameY : (subdivisionSegment source drawing first.1).start.2 = (subdivisionSegment source drawing second.1).start.2 := by
    simp only [subdivisionSegment,sameVertex]
  rcases lt_trichotomy 0 (subdivisionSegment source drawing first.1).direction.1 with firstRight | firstVertical | firstLeft
  · rcases lt_trichotomy 0 (subdivisionSegment source drawing second.1).direction.1 with secondRight | secondVertical | secondLeft
    · exact right_source_coreRoutes_disjoint planar degree graphLocal drawingLocal firstMember secondMember firstRight secondRight
        sameVertex different firstContains secondContains
    · have firstBound := coreRoute_right_source_bound planar degree firstMember firstRight firstContains
      have secondBound := coreRoute_vertical_x planar degree secondMember secondVertical.symm secondContains
      rw [sameX] at firstBound
      linarith
    · have firstBound := coreRoute_right_source_bound planar degree firstMember firstRight firstContains
      have secondBound := coreRoute_left_source_bound planar degree secondMember secondLeft secondContains
      rw [sameX] at firstBound
      linarith
  · have firstZero := firstVertical.symm
    rcases lt_trichotomy 0 (subdivisionSegment source drawing second.1).direction.1 with secondRight | secondVertical | secondLeft
    · have firstBound := coreRoute_vertical_x planar degree firstMember firstZero firstContains
      have secondBound := coreRoute_right_source_bound planar degree secondMember secondRight secondContains
      rw [sameX] at firstBound
      linarith
    · have secondZero := secondVertical.symm
      have firstKey := vertical_source_portRayKey source drawing firstMember firstZero
      have secondKey := vertical_source_portRayKey source drawing secondMember secondZero
      have keysNe : (shiftedDrawing source drawing).portRayKey (sourcePort first.1 first.2) ≠
          (shiftedDrawing source drawing).portRayKey (sourcePort second.1 second.2) := by
        intro equal
        exact different (shifted_distinctPortRayKeys planar _ (sourcePort_mem_allPorts _ firstMember)
          _ (sourcePort_mem_allPorts _ secondMember) sameVertex equal)
      by_cases firstUp : 0 < (subdivisionSegment source drawing first.1).direction.2
      · by_cases secondUp : 0 < (subdivisionSegment source drawing second.1).direction.2
        · exact keysNe (by rw [firstKey,secondKey,if_pos firstUp,if_pos secondUp])
        · have secondDown : (subdivisionSegment source drawing second.1).direction.2 < 0 := by
            have nonzero := vertical_direction_nonzero planar secondMember secondZero
            omega
          have firstBound := coreRoute_up_source_bound planar degree firstMember firstZero firstUp firstContains
          have secondBound := coreRoute_down_source_bound planar degree secondMember secondZero secondDown secondContains
          rw [sameY] at firstBound
          linarith
      · by_cases secondUp : 0 < (subdivisionSegment source drawing second.1).direction.2
        · have firstDown : (subdivisionSegment source drawing first.1).direction.2 < 0 := by
            have nonzero := vertical_direction_nonzero planar firstMember firstZero
            omega
          have firstBound := coreRoute_down_source_bound planar degree firstMember firstZero firstDown firstContains
          have secondBound := coreRoute_up_source_bound planar degree secondMember secondZero secondUp secondContains
          rw [sameY] at firstBound
          linarith
        · exact keysNe (by rw [firstKey,secondKey,if_neg firstUp,if_neg secondUp])
    · have firstBound := coreRoute_vertical_x planar degree firstMember firstZero firstContains
      have secondBound := coreRoute_left_source_bound planar degree secondMember secondLeft secondContains
      rw [sameX] at firstBound
      linarith
  · rcases lt_trichotomy 0 (subdivisionSegment source drawing second.1).direction.1 with secondRight | secondVertical | secondLeft
    · have firstBound := coreRoute_left_source_bound planar degree firstMember firstLeft firstContains
      have secondBound := coreRoute_right_source_bound planar degree secondMember secondRight secondContains
      rw [sameX] at firstBound
      linarith
    · have firstBound := coreRoute_left_source_bound planar degree firstMember firstLeft firstContains
      have secondBound := coreRoute_vertical_x planar degree secondMember secondVertical.symm secondContains
      rw [sameX] at firstBound
      linarith
    · exact left_source_coreRoutes_disjoint planar degree graphLocal drawingLocal firstMember secondMember firstLeft secondLeft
        sameVertex different firstContains secondContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
