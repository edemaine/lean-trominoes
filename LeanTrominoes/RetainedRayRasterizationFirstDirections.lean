/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.RetainedRayRasterization
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-! # First directions of retained-ray rasterizations

The retained planar drawing may use diagonal compass rays and the three
non-octilinear routed-clause rays.  Rasterization replaces their first
straight segment by a deterministic orthogonal staircase.  This file exposes
the resulting cardinal exit without inspecting the rest of the polyline.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A positive retained ray rasterizes to a route with a genuine first
cardinal direction. -/
theorem RetainedRay.rasterize_firstDirection_isGenuine
    (ray : RetainedRay) (start : Cell)
    (positive : 0 < match ray with
      | .compass _ length => length
      | .routedClause _ length => length) :
    (AxisDirection.polylineFirstDirection
      (ray.rasterize start)).IsGenuine := by
  cases ray with
  | compass port length =>
      cases length with
      | zero => simp at positive
      | succ length =>
          have lengthPositiveInt : (0 : Int) < length + 1 := by omega
          have negativeSuccNe : (-1 : Int) + -length ≠ 0 := by omega
          have positiveSuccNe : (length : Int) + 1 ≠ 0 := by omega
          have negativeOneLt : (-1 : Int) < length := by omega
          have notLtNegativeOne : ¬(length : Int) < -1 := by omega
          cases port <;>
            simp [RetainedRay.rasterize, compassRay,
              diagonalStaircase, AxisDirection.polylineFirstDirection,
              AxisDirection.between, AxisDirection.IsGenuine,
              OccurrenceSplitRing.Port.unitVector,
              Cell.add, Cell.scale, lengthPositiveInt,
              negativeSuccNe, positiveSuccNe,
              negativeOneLt, notLtNegativeOne]
  | routedClause arm length =>
      cases length with
      | zero => simp at positive
      | succ length =>
          cases arm <;>
            simp [RetainedRay.rasterize, routedClauseRay,
              routedClauseRayBlock, routedClauseRayOffsets,
              joinAtEndpoint, AxisDirection.polylineFirstDirection,
              AxisDirection.between, AxisDirection.IsGenuine,
              Cell.add]

/-- A supported retained segment rasterizes to a route with a genuine first
cardinal direction. -/
theorem rasterizeRetainedSegment_firstDirection_isGenuine
    (segment : GridSegment)
    (retained :
      RetainedRayVector
        (Cell.sub segment.finish segment.start)) :
    (AxisDirection.polylineFirstDirection
      (rasterizeRetainedSegment segment)).IsGenuine := by
  unfold RetainedRayVector at retained
  unfold rasterizeRetainedSegment
  generalize classified :
    retainedRayClassify
      (Cell.sub segment.finish segment.start) = classifiedRay
  cases classifiedRay with
  | none => simp [classified] at retained
  | some ray =>
      exact ray.rasterize_firstDirection_isGenuine segment.start
        (retainedRayClassify_sound classified).1

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => rfl

/-- The first direction of a retained-ray rasterized polyline is determined
entirely by the rasterization of its first source segment. -/
theorem rasterizeRetainedPolyline_firstDirection_cons_cons
    (first second : Cell) (rest : List Cell)
    (retained :
      RetainedRayVector (Cell.sub second first)) :
    AxisDirection.polylineFirstDirection
        (rasterizeRetainedPolyline (first :: second :: rest)) =
      AxisDirection.polylineFirstDirection
        (rasterizeRetainedSegment (GridSegment.mk first second)) := by
  rw [rasterizeRetainedPolyline_cons_cons]
  exact polylineFirstDirection_joinAtEndpoint_of_genuine
    (rasterizeRetainedSegment_firstDirection_isGenuine
      (GridSegment.mk first second) retained)

/-- A retained polyline with a genuine first segment exposes the same local
rasterized first direction regardless of its later segments. -/
theorem rasterizeRetainedPolyline_firstDirection
    {points : List Cell}
    (length : 2 ≤ points.length)
    (retained : RetainedRayPolyline points) :
    ∃ first second rest,
      points = first :: second :: rest ∧
      AxisDirection.polylineFirstDirection
          (rasterizeRetainedPolyline points) =
        AxisDirection.polylineFirstDirection
          (rasterizeRetainedSegment (GridSegment.mk first second)) := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          refine ⟨first, second, rest, rfl, ?_⟩
          apply rasterizeRetainedPolyline_firstDirection_cons_cons
          exact retained (GridSegment.mk first second)
            (by simp [gridPolylineSegments])

/-- Rasterization preserves the first direction of a nondegenerate retained
polyline whose source segments are already axis aligned. -/
theorem rasterizeRetainedPolyline_firstDirection_eq
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (retained : RetainedRayPolyline points) :
    AxisDirection.polylineFirstDirection
        (rasterizeRetainedPolyline points) =
      AxisDirection.polylineFirstDirection points := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          rw [rasterizeRetainedPolyline_firstDirection_cons_cons
            first second rest
            (retained (GridSegment.mk first second)
              (by simp [gridPolylineSegments]))]
          rw [rasterizeRetainedSegment_eq_of_axisAligned]
          · rfl
          · exact (List.isChain_cons_cons.mp orthogonal).1

end PeriodicEightOccurrenceSplit
end LeanTrominoes
