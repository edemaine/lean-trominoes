/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPortSpacing
import LeanTrominoes.PeriodicGridDrawingRawBendVerticalFanGeometry
import LeanTrominoes.OrthogonalCubicRefinementBounds
import LeanTrominoes.GridSegmentRationalSlopeOrder
import LeanTrominoes.GridSegmentScaledOrderedTubes
import LeanTrominoes.GridSegmentBoundedCoreReflection

/-! # Orientation-independent incidence data for cubic digital cores

The raw ray and its perturbed core may be viewed from either endpoint and
translated to any periodic copy. Separation depends only on these data.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

structure IncidentCoreData {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) (raw core : GridSegment) : Prop where
  member : port ∈ allPorts (subdivisionGraph source drawing)
  key : (shiftedDrawing source drawing).portRayKey port = raw.straightRayKey
  genuine : raw.start ≠ raw.finish
  bounds : |raw.direction.1| ≤ 2*(drawing.gridSize : Int) ∧ |raw.direction.2| ≤ 2*(drawing.gridSize : Int)
  perturbed : GridSegment.BoundedEndpointPerturbation 10 (Cubic.coreFactor drawing.gridSize) raw core
  start : core.start = Cell.add (Cell.scale (Cubic.coreFactor drawing.gridSize) raw.start) (fanAnchor source drawing port)
  vertical : raw.direction.1 = 0 → core.start.1 = core.finish.1

namespace IncidentCoreData

theorem right_key {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (right : 0 < raw.direction.1) : (shiftedDrawing source drawing).portRayKey port = .right raw.rationalSlope := by
  rw [data.key,GridSegment.straightRayKey_of_right right]

theorem left_key {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (left : raw.direction.1 < 0) : (shiftedDrawing source drawing).portRayKey port = .left raw.rationalSlope := by
  rw [data.key,GridSegment.straightRayKey_of_left left]

theorem vertical_key {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (vertical : raw.direction.1 = 0) :
    (shiftedDrawing source drawing).portRayKey port = if 0 < raw.direction.2 then .up else .down := by
  have sameX : raw.start.1 = raw.finish.1 := by simp only [GridSegment.direction] at vertical; omega
  have yOrder : raw.start.2 < raw.finish.2 ↔ 0 < raw.direction.2 := by simp only [GridSegment.direction]; omega
  simp only [data.key,GridSegment.straightRayKey,sameX,lt_self_iff_false,ite_false,yOrder]

theorem vertical_direction_nonzero {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core)
    (vertical : raw.direction.1 = 0) : raw.direction.2 ≠ 0 := by
  intro zero
  apply data.genuine
  simp only [GridSegment.direction] at vertical zero
  apply Prod.ext <;> omega

theorem ordered_right_tubes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {firstPort secondPort : GraphPort (Vertex V)} {first second firstCore secondCore : GridSegment}
    (firstData : IncidentCoreData source drawing firstPort first firstCore)
    (secondData : IncidentCoreData source drawing secondPort second secondCore)
    (sameVertex : firstPort.vertex = secondPort.vertex) (sameStart : first.start = second.start)
    (firstRight : 0 < first.direction.1) (secondRight : 0 < second.direction.1)
    (slopes : first.rationalSlope < second.rationalSlope) {point : ℝ × ℝ}
    (firstContains : (firstCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point) :
    ¬(secondCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point := by
  have firstKey := firstData.right_key firstRight
  have secondKey := secondData.right_key secondRight
  have gap := fanAnchor_right_gap planar degree firstData.member secondData.member sameVertex firstKey secondKey slopes
  have firstAnchor := fanAnchor_x planar degree firstData.member
  have secondAnchor := fanAnchor_x planar degree secondData.member
  simp only [firstKey,BendFan.horizontalSign,mul_one] at firstAnchor
  simp only [secondKey,BendFan.horizontalSign,mul_one] at secondAnchor
  have column : firstCore.start.1 = secondCore.start.1 := by
    simp only [firstData.start,secondData.start,Cell.add,Cell.scale,sameStart,firstAnchor,secondAnchor]
  have ports : firstCore.start.2+2 ≤ secondCore.start.2 := by
    simp only [firstData.start,secondData.start,Cell.add,Cell.scale,sameStart]
    omega
  have firstSlope := GridSegment.perturbed_right_core_slope firstData.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) firstRight firstData.bounds.2
  have secondSlope := GridSegment.perturbed_right_core_slope secondData.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) secondRight secondData.bounds.2
  have order := GridSegment.cross_positive_of_bounded_perturbation (by positivity) (by norm_num)
    (Cubic.coreFactor_cross_spacing drawing.gridSize) firstData.bounds secondData.bounds
    firstData.perturbed.direction secondData.perturbed.direction
    ((GridSegment.cross_positive_iff_right_slope_order firstRight secondRight).mpr slopes)
  exact GridSegment.ordered_right_scaled_tubes_disjoint (by positivity)
    (by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize) firstSlope.1 secondSlope.1 column ports
    order.le secondSlope.2 (by have spacing := Cubic.rasterFactor_slope_spacing drawing.gridSize; omega) firstContains

theorem ordered_left_tubes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {firstPort secondPort : GraphPort (Vertex V)} {first second firstCore secondCore : GridSegment}
    (firstData : IncidentCoreData source drawing firstPort first firstCore)
    (secondData : IncidentCoreData source drawing secondPort second secondCore)
    (sameVertex : firstPort.vertex = secondPort.vertex) (sameStart : first.start = second.start)
    (firstLeft : first.direction.1 < 0) (secondLeft : second.direction.1 < 0)
    (slopes : second.rationalSlope < first.rationalSlope) {point : ℝ × ℝ}
    (firstContains : (firstCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point) :
    ¬(secondCore.scale (Cubic.rasterFactor drawing.gridSize)).RealTubeContains 3 point := by
  have firstKey := firstData.left_key firstLeft
  have secondKey := secondData.left_key secondLeft
  have gap := fanAnchor_left_gap planar degree secondData.member firstData.member sameVertex.symm secondKey firstKey slopes
  have firstAnchor := fanAnchor_x planar degree firstData.member
  have secondAnchor := fanAnchor_x planar degree secondData.member
  simp only [firstKey,BendFan.horizontalSign,mul_neg_one] at firstAnchor
  simp only [secondKey,BendFan.horizontalSign,mul_neg_one] at secondAnchor
  have column : firstCore.start.1 = secondCore.start.1 := by
    simp only [firstData.start,secondData.start,Cell.add,Cell.scale,sameStart,firstAnchor,secondAnchor]
  have ports : firstCore.start.2+2 ≤ secondCore.start.2 := by
    simp only [firstData.start,secondData.start,Cell.add,Cell.scale,sameStart]
    omega
  have firstSlope := GridSegment.perturbed_left_core_slope firstData.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) firstLeft firstData.bounds.2
  have secondSlope := GridSegment.perturbed_left_core_slope secondData.perturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) secondLeft secondData.bounds.2
  have rawOrder : GridSegment.cross first.direction second.direction < 0 := by
    have positive := (GridSegment.cross_positive_iff_left_slope_order secondLeft firstLeft).mpr slopes
    simp only [GridSegment.cross] at positive ⊢
    nlinarith
  have order := GridSegment.cross_negative_of_bounded_perturbation (by positivity) (by norm_num)
    (Cubic.coreFactor_cross_spacing drawing.gridSize) firstData.bounds secondData.bounds
    firstData.perturbed.direction secondData.perturbed.direction rawOrder
  exact GridSegment.ordered_left_scaled_tubes_disjoint (by positivity)
    (by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize) firstSlope.1 secondSlope.1 column ports
    order.le secondSlope.2 (by have spacing := Cubic.rasterFactor_slope_spacing drawing.gridSize; omega) firstContains

end IncidentCoreData
end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
