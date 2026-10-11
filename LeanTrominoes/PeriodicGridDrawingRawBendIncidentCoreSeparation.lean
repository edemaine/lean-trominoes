/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentCoreGeometry

/-! # Incidence-core separation for arbitrary endpoint orientations and copies -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem horizontal_tubes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {firstPort secondPort : GraphPort (Vertex V)} {first second firstCore secondCore : GridSegment}
    (firstData : IncidentCoreData source drawing firstPort first firstCore)
    (secondData : IncidentCoreData source drawing secondPort second secondCore)
    (sameVertex : firstPort.vertex = secondPort.vertex) (sameStart : first.start = second.start)
    (different : firstPort ≠ secondPort)
    (sameSide : (0 < first.direction.1 ∧ 0 < second.direction.1) ∨
      (first.direction.1 < 0 ∧ second.direction.1 < 0)) {point : ℝ × ℝ}
    (firstTube : (firstCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point) :
    ¬(secondCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point := by
  intro secondTube
  rcases sameSide with ⟨firstRight,secondRight⟩ | ⟨firstLeft,secondLeft⟩
  · have slopesNe : first.rationalSlope ≠ second.rationalSlope := by
      intro equal
      exact different (shifted_distinctPortRayKeys planar _ firstData.member _ secondData.member sameVertex
        (by rw [firstData.right_key firstRight,secondData.right_key secondRight,equal]))
    rcases lt_or_gt_of_ne slopesNe with ordered | ordered
    · exact firstData.ordered_right_tubes_disjoint planar degree secondData sameVertex sameStart firstRight secondRight ordered firstTube secondTube
    · exact secondData.ordered_right_tubes_disjoint planar degree firstData sameVertex.symm sameStart.symm secondRight firstRight ordered secondTube firstTube
  · have slopesNe : first.rationalSlope ≠ second.rationalSlope := by
      intro equal
      exact different (shifted_distinctPortRayKeys planar _ firstData.member _ secondData.member sameVertex
        (by rw [firstData.left_key firstLeft,secondData.left_key secondLeft,equal]))
    rcases lt_or_gt_of_ne slopesNe with ordered | ordered
    · exact secondData.ordered_left_tubes_disjoint planar degree firstData sameVertex.symm sameStart.symm secondLeft firstLeft ordered secondTube firstTube
    · exact firstData.ordered_left_tubes_disjoint planar degree secondData sameVertex sameStart firstLeft secondLeft ordered firstTube secondTube

theorem disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {firstPort secondPort : GraphPort (Vertex V)} {first second firstCore secondCore : GridSegment}
    (firstData : IncidentCoreData source drawing firstPort first firstCore)
    (secondData : IncidentCoreData source drawing secondPort second secondCore)
    (sameVertex : firstPort.vertex = secondPort.vertex) (sameStart : first.start = second.start)
    (different : firstPort ≠ secondPort) {point : ℝ × ℝ}
    (firstTube : (firstCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point)
    (secondTube : (secondCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point)
    (firstBox : (firstCore.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point)
    (secondBox : (secondCore.scale (Cubic.rasterFactor drawing.gridSize)).RealBoxContains point) : False := by
  have rasterPositive : (0 : ℝ) < Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have sameX := congrArg Prod.fst sameStart
  have sameY := congrArg Prod.snd sameStart
  rcases lt_trichotomy 0 first.direction.1 with firstRight | firstVertical | firstLeft
  · rcases lt_trichotomy 0 second.direction.1 with secondRight | secondVertical | secondLeft
    · exact firstData.horizontal_tubes_disjoint planar degree secondData sameVertex sameStart different
        (Or.inl ⟨firstRight,secondRight⟩) firstTube secondTube
    · have firstBound := firstData.right_bound planar degree firstRight firstBox
      have secondBound := secondData.vertical_x planar degree secondVertical.symm secondBox
      rw [sameX] at firstBound
      linarith
    · have firstBound := firstData.right_bound planar degree firstRight firstBox
      have secondBound := secondData.left_bound planar degree secondLeft secondBox
      rw [sameX] at firstBound
      linarith
  · have firstZero := firstVertical.symm
    rcases lt_trichotomy 0 second.direction.1 with secondRight | secondVertical | secondLeft
    · have firstBound := firstData.vertical_x planar degree firstZero firstBox
      have secondBound := secondData.right_bound planar degree secondRight secondBox
      rw [sameX] at firstBound
      linarith
    · have secondZero := secondVertical.symm
      have firstKey := firstData.vertical_key firstZero
      have secondKey := secondData.vertical_key secondZero
      have keysNe : (shiftedDrawing source drawing).portRayKey firstPort ≠
          (shiftedDrawing source drawing).portRayKey secondPort := by
        intro equal
        exact different (shifted_distinctPortRayKeys planar _ firstData.member _ secondData.member sameVertex equal)
      by_cases firstUp : 0 < first.direction.2
      · by_cases secondUp : 0 < second.direction.2
        · exact keysNe (by rw [firstKey,secondKey,if_pos firstUp,if_pos secondUp])
        · have firstBound := firstData.vertical_y planar degree firstZero firstBox
          have secondBound := secondData.vertical_y planar degree secondZero secondBox
          rw [if_pos firstUp,sameY] at firstBound
          rw [if_neg secondUp] at secondBound
          linarith
      · by_cases secondUp : 0 < second.direction.2
        · have firstBound := firstData.vertical_y planar degree firstZero firstBox
          have secondBound := secondData.vertical_y planar degree secondZero secondBox
          rw [if_neg firstUp,sameY] at firstBound
          rw [if_pos secondUp] at secondBound
          linarith
        · exact keysNe (by rw [firstKey,secondKey,if_neg firstUp,if_neg secondUp])
    · have firstBound := firstData.vertical_x planar degree firstZero firstBox
      have secondBound := secondData.left_bound planar degree secondLeft secondBox
      rw [sameX] at firstBound
      linarith
  · rcases lt_trichotomy 0 second.direction.1 with secondRight | secondVertical | secondLeft
    · have firstBound := firstData.left_bound planar degree firstLeft firstBox
      have secondBound := secondData.right_bound planar degree secondRight secondBox
      rw [sameX] at firstBound
      linarith
    · have firstBound := firstData.left_bound planar degree firstLeft firstBox
      have secondBound := secondData.vertical_x planar degree secondVertical.symm secondBox
      rw [sameX] at firstBound
      linarith
    · exact firstData.horizontal_tubes_disjoint planar degree secondData sameVertex sameStart different
        (Or.inr ⟨firstLeft,secondLeft⟩) firstTube secondTube

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision.IncidentCoreData
