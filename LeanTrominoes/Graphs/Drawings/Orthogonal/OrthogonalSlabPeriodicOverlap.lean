/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalSlabRouteGeometry
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.Geometry.GridSegmentRealConvexity

/-! # A dogleg spanning more than one period overlaps its translated copy

Finite slab separation alone does not prove periodic separation. In the
global refinement, long vertical movements must be split at row seams.
-/
namespace LeanTrominoes.OrthogonalSlabRouting
open PeriodicOrthocrossing

theorem periodic_vertical_track_overlap {left right track source target period : Int}
    (inside : left < track ∧ track < right) (positive : 0 < period) (long : source+period < target) :
    ∃ point : ℝ × ℝ,
      GridPolyline.RealContains (route left right track source target) point ∧
      GridPolyline.RealContains (translatePolyline (0,period) (route left right track source target)) point ∧
      ¬GridPolyline.RealIsEndpoint (route left right track source target) point := by
  let point := realCell (track,source+period)
  have firstContains : GridPolyline.RealContains (route left right track source target) point := by
    apply (route_image inside point).mpr
    refine ⟨⟨(track,source),(track,target)⟩,by simp [segments],?_⟩
    apply GridSegment.realContains_of_contains
    right
    refine ⟨⟨rfl,by change source ≠ target; omega⟩,rfl,Or.inl ?_⟩
    change source ≤ source+period ∧ source+period ≤ target
    exact ⟨by omega,by omega⟩
  have secondStart : GridPolyline.RealContains (route left right track source target) (realCell (track,source)) := by
    apply (route_image inside _).mpr
    exact ⟨⟨(left,source),(track,source)⟩,by simp [segments],GridSegment.realContains_finish _⟩
  have translated := (GridPolyline.realContains_translate (0,period) (route left right track source target) _).mpr secondStart
  have secondContains : GridPolyline.RealContains (translatePolyline (0,period) (route left right track source target)) point := by
    simpa [point,realCell,add_comm] using translated
  refine ⟨point,firstContains,secondContains,?_⟩
  intro endpoint
  rcases endpoint with ⟨first,firstHead,equal⟩ | ⟨last,lastEnd,equal⟩
  · rw [route_head] at firstHead
    have endpointEq := Option.some.inj firstHead
    have hx := congrArg Prod.fst equal
    simp only [point,realCell,← endpointEq] at hx
    have same : track = left := by exact_mod_cast hx
    omega
  · rw [route_last] at lastEnd
    have endpointEq := Option.some.inj lastEnd
    have hx := congrArg Prod.fst equal
    simp only [point,realCell,← endpointEq] at hx
    have same : track = right := by exact_mod_cast hx
    omega

end LeanTrominoes.OrthogonalSlabRouting
