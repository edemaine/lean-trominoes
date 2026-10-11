/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendDigitalCores
import LeanTrominoes.GridSegmentBoundedCoreReflection

/-! # Incident leftward cores stay disjoint with the selected linear factors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem ordered_left_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstLeft : (subdivisionSegment source drawing first.1).direction.1 < 0)
    (secondLeft : (subdivisionSegment source drawing second.1).direction.1 < 0)
    (sameColumn : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.1 =
      (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.1)
    (ports : (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) first).start.2+2 ≤
      (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) second).start.2)
    (ordered : GridSegment.cross (subdivisionSegment source drawing first.1).direction
      (subdivisionSegment source drawing second.1).direction < 0)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (coreRoute source drawing first) point) :
    ¬GridPolyline.RealContains (coreRoute source drawing second) point := by
  intro secondContains
  have firstBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal firstMember
  have secondBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal secondMember
  have firstPerturbed := anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) first
  have secondPerturbed := anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) second
  have firstSlope := GridSegment.perturbed_left_core_slope firstPerturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) firstLeft firstBounds.2
  have secondSlope := GridSegment.perturbed_left_core_slope secondPerturbed (by norm_num) (by positivity)
    (Cubic.coreFactor_slope_spacing drawing.gridSize) secondLeft secondBounds.2
  have coreOrder := GridSegment.cross_negative_of_bounded_perturbation (by positivity) (by norm_num)
    (Cubic.coreFactor_cross_spacing drawing.gridSize) firstBounds secondBounds firstPerturbed.direction secondPerturbed.direction ordered
  have firstNonzero := ne_of_lt firstLeft
  have secondNonzero := ne_of_lt secondLeft
  have firstNotRight := not_lt_of_ge firstLeft.le
  have secondNotRight := not_lt_of_ge secondLeft.le
  simp only [coreRoute,if_neg firstNonzero,if_neg secondNonzero,coreSide,if_neg firstNotRight,if_neg secondNotRight] at firstContains secondContains
  exact GridSegment.ordered_left_kickedDigitalRoutes_disjoint (by positivity)
    (by exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize)
    firstSlope.1 secondSlope.1 sameColumn ports coreOrder.le secondSlope.2
    (by have spacing := Cubic.rasterFactor_slope_spacing drawing.gridSize; omega) firstContains secondContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
